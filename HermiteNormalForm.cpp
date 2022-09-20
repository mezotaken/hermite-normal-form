#include <iostream>
#include <vector>
#include <algorithm>

// Печать матрицы

template<typename T>
void PrintMatrix(const std::vector<std::vector<T>> &in_matrix) {
    for (unsigned int i = 0; i < in_matrix.size(); i++) {
        for (unsigned int j = 0; j < in_matrix[0].size(); j++)
            std::cout << in_matrix[i][j] << " ";
        std::cout << "\n";
    }
    std::cout << "\n";
}

// Получение основания для будущей редукции по модулю. 
// |det minor|, где minor - любой минор матрицы A ранга m
// Сложность O(m*n^2), метод Гаусса.
// Преполагается, что матрица имеет минор ранга m при размере m x n
// и m < n

int GetModulo(const std::vector<std::vector<int>> &in_matrix) {
    int m = in_matrix.size();
    int n = in_matrix[0].size();
    std::vector<std::vector<double>> matr(m, std::vector<double>(n));
    double res = 1;
    for (int i = 0; i < m; i++)
        for (int j = 0; j < n; j++)
            matr[i][j] = in_matrix[i][j];

    for (int i = 0; i < m; i++) {
        int skip = 0;
        while (matr[i][i + skip] == 0) {
            if (i + 1 < m) {
                int z = 1;
                while (matr[i + z][i + skip + z] == 0)
                    z++;
                if (matr[i + z][i + skip + z] != 0)
                    std::swap(matr[i], matr[i + z]);
                else
                    skip += 1;
            } else {
                skip += 1;
            }
        }
        res *= matr[i][i + skip];
        for (int j = i + 1; j < m; j++) {
            double factor = -matr[j][i + skip] / matr[i][i + skip];

            for (int k = i + skip; k < n; k++) {
                matr[j][k] += matr[i][k] * factor;
            }

        }
        
    }
    return abs(round(res));
}


// Приведение a в диапазон [0, b - 1]

inline int mod(int a, int b)
{
    int r = a % b;
    return r < 0 ? r + b : r;
}

// Редукция столбцов матрицы D друг с другом
// Вход: уровень, с которого начинается редукция,
// Индексы столбцов, которые нужно редуцировать
// Выход: индекс нового опорного столбца (другой занулён на уровне k)

int ReduceColumns(std::vector<std::vector<int>>& mat, int k, int i, int j, int modulo) {
    int piv = i;
    int target = j;
    while (mat[k][target] != 0) {
        if (mat[k][target] < mat[k][piv])
            std::swap(piv, target);

        // Деление целочисленное, округление вниз автоматическое

        int f = mat[k][target] / mat[k][piv];

        for (int z = k; z < mat.size(); z++) {
            mat[z][target] -= mat[z][piv] * f;
        }
    }
    // Приведение изменённых столбцов, к которым не вернёмся к диапазону [0,M]
    for (int z = k; z < mat.size(); z++)
        if (mat[z][target] > modulo || mat[z][target] < 0)
            mat[z][target] = mod(mat[z][target], modulo);
    return piv;
}

// Последний шаг алгоритма для получения H.
// Уже нижнетреугольная матрица приводится к такому виду, что
// Диагональные элементы строго положительны
// Элементы ниже диагонали неотрицательны
// Любой элемент строки ниже диагонали не превосходят соответствующего диагонального элемента

void FinalFix(std::vector<std::vector<int>>& mat) {
    int m = mat.size();
    for (int i = 1; i < m; i++) {
        int diag = mat[i][i];
        for (int j = 0; j < i; j++) {
            int targ = mat[i][j];
            int f = targ/diag;
            if (targ < 0)
                f--;
            if (targ < 0 || targ > diag)
                for (int k = i; k < m; k++)
                    mat[k][j] -= mat[k][i] * f;
        }
    }
}

// Вычисление эрмитовой нормальной формы H:
// A*U = H, где |det U| = 1 (унимодулярная)
// Сложность O(m*n*log2(M)), M = modulo
// Вызов метода Гаусса отдельно, 
// чтобы можно было замерить время работы без него.

 std::vector<std::vector<int>> HermitNormalForm(const std::vector<std::vector<int>> &in_matrix, int modulo) {
    int m = in_matrix.size();
    int n = in_matrix[0].size();
    
    std::vector<std::vector<int>> res(in_matrix);

    for (int i = 0; i < m; i++) {
        res[i].resize(n + m);
        res[i][n + i] = modulo;
    }

    // На этом моменте в res находится расширенная матрица размера
    // (m) x (n+m)


    for (int k = 0; k < m; k++) {
        
        // Редукция первой строки D до единственного ненулевого элемента
        int piv_ind = -1;
        for (int j = k; j < k + n + 1; j++) {
            if(res[k][j] < 0) 
                res[k][j] = mod(res[k][j], modulo);
            if (res[k][j] == 0)
                continue;

            if (piv_ind == -1)
                piv_ind = j;
            if (piv_ind != j) 
                piv_ind = ReduceColumns(res, k, piv_ind, j, modulo);
        }

        // Перенос единственного ведущего столбца в начало матрицы D
        // Чтобы образовать нижнетреугольную матрицу B 
        // Предварительно он приводится к диапазону [0, M]
        // Так как в функции редукции он не привёлся.
        for (int i = k; i < m; i++) {
            if (res[i][piv_ind] > modulo || res[i][piv_ind] < 0)
                res[i][piv_ind] = mod(res[i][piv_ind], modulo);
            std::swap(res[i][piv_ind], res[i][k]);
        }
    }

    // На этом моменте res - матрица вида [B, 0], количество
    // Столбцов - m штук, они отрезаются. B - нижнетреугольная
    
    for (int i = 0; i < m; i++)
        res[i].resize(n);

    // Приведение к каноничному для H виду, см. описание функции
    FinalFix(res);

    return res;
}



int main()
{
    std::vector<std::vector<int>> mat{ {{-1,  0,-1,7,4}, { 3, 2,-3,5,3}, {3,5,-2,-9,-15 },{5,5,1,0,0},{8,5,7,1,6}} };
    std::cout << "Matrix A: \n";
    PrintMatrix(mat);

    int m = GetModulo(mat);
    std::cout << "M = " << m << "\n\n";

    std::vector<std::vector<int>> res = HermitNormalForm(mat, m);
    std::cout<< "Hermite Normal Form H: \n";
    PrintMatrix(res);
}
