-- Prove2me | Theorems.Thm_UnderstandingML_pca_theorem
-- name    : UnderstandingML.pca_theorem
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:22:33.774976+00:00
-- url     : https://prove2.me/theorems/8c04c2f8-5a08-4359-a2c5-4e2f8880fb4d
-- title:
--   Theorem 23.2: with A = ∑ xᵢxᵢᵀ = V diag(D) Vᵀ, D nonincreasing, the first n columns of V with W = Uᵀ minimize the PCA objective (23.1)
-- statement:
--   **Theorem 23.2.** Let $x_1, \dots, x_m$ be arbitrary vectors in $\mathbb{R}^d$, let $A = \sum_{i=1}^m x_ix_i^\top$, and let $u_1, \dots, u_n$ be $n$ eigenvectors of the matrix $A$ corresponding to the largest $n$ eigenvalues of $A$. Then, the solution to the PCA optimization problem given in Equation (23.1) is to set $U$ to be the matrix whose columns are $u_1, \dots, u_n$ and to set $W = U^\top$.
--
--   Formally: $u_1, \dots, u_n$ are the first $n$ columns of a spectral decomposition $A = V\operatorname{diag}(D)V^\top$ with $V^\top V = I$ and $D$ nonincreasing, and $(U, U^\top)$ has objective at most that of every $(U', W')$; $n \le d$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §23.1 pp. 325-326, Theorem 23.2 with its proof

import Definitions.Def_UnderstandingML_DimReduction

open MeasureTheory ProbabilityTheory

namespace UnderstandingML

/-- **Theorem 23.2** (p. 325). Let `x₁, …, x_m` be arbitrary vectors in `ℝ^d`, let
`A = ∑ᵢ xᵢxᵢᵀ`, and let `u₁, …, u_n` be `n` eigenvectors of the matrix `A` corresponding to the
largest `n` eigenvalues of `A`. Then the solution to the PCA optimization problem (23.1) is to
set `U` to be the matrix whose columns are `u₁, …, u_n` and to set `W = Uᵀ`.
The eigenvectors are the first `n` columns of a spectral decomposition `A = V diag(D) Vᵀ`,
`VᵀV = I`, with `D` nonincreasing; `n ≤ d`. -/
theorem pca_theorem {m d n : ℕ} (hn : n ≤ d) (x : Fin m → Fin d → ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hV : V.transpose * V = 1) (D : Fin d → ℝ) (hD : Antitone D)
    (hA : scatterMatrix x = V * Matrix.diagonal D * V.transpose)
    (U : Matrix (Fin d) (Fin n) ℝ) (W : Matrix (Fin n) (Fin d) ℝ) :
    pcaObjective x (V.submatrix id (Fin.castLE hn)) (V.submatrix id (Fin.castLE hn)).transpose ≤
      pcaObjective x U W := by sorry

end UnderstandingML
