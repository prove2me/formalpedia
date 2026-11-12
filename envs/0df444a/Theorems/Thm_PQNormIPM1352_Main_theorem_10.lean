-- Prove2me | Theorems.Thm_PQNormIPM1352_Main_theorem_10
-- name    : PQNormIPM1352.Main.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:43.571615+00:00
-- url     : https://prove2.me/theorems/ebed6c66-0c23-4c99-8b50-1ac0eb53c0d3
-- title:
--   Theorem 10 — $H\setminus\gamma = M + VV^\top$ with $M$ an M-matrix, $\le4s$ non-zeros, $DMD$ strictly diagonally dominant
-- statement:
--   Let $p\ge q>1$, let the support $S$ ($s$ entries) have no all-zero row or column, and let $x = (z,y,\gamma)\in\mathrm{int}(K)$. Let $H = \nabla^2F(x)$ be the Hessian of the barrier (6) in the block form (26), $w = (z,y)$, and
--   $$H\setminus\gamma = H_w - H_{w\gamma}H_\gamma^{-1}H_{w\gamma}^\top$$
--   its Schur complement with respect to $\gamma$. With $Z = \sum_i z(i)$, $Y = \sum_j y(j)$, let
--   $$V = \begin{pmatrix}\mathbf 1_m/(1-Z) & 0\\ 0 & \mathbf 1_n/(1-Y)\end{pmatrix}\in\mathbb R^{(m+n)\times2},\qquad M = H\setminus\gamma - VV^\top,$$
--   so that $H\setminus\gamma = M + VV^\top$. Then:
--   1. $M\in\mathbb R^{(m+n)\times(m+n)}$ is a symmetric M-matrix (positive semidefinite with non-positive off-diagonal entries);
--   2. $M$ has at most $4s$ non-zero entries;
--   3. $D = \mathrm{Diag}(z, y)$ has positive diagonal entries, and $DMD$ is strictly diagonally dominant.
--
--   This structure is what lets each Newton step be computed with one Laplacian-type solve and a rank-2 Woodbury correction (Algorithms 3–4).
--
--   Differences from the source:
--   - encoding: the non-negative matrix after removing all-zero rows and columns, a standing assumption of §3 (p. 7) → a sparsity pattern with every row and column occupied (`Preprocessed`) and the barrier on ℝ^{m+n+s}; reason: the paper removes such rows and columns before (5) and works with the support S only
--   - generalization: H \ γ can be written as M + VVᵀ for some M ∈ ℝ^{(m+n)×(m+n)} with the stated properties and some V ∈ ℝ^{(m+n)×2} → the specific V = (1_m/(1−Z), 0; 0, 1_n/(1−Y)) of the proof (p. 13) and M = H \ γ − VVᵀ have the properties; reason: exhibiting the witnesses implies the existential statement; they are the matrices Algorithm 4 uses
--   - encoding: symmetric M-matrix (§2.1.2) → positive semidefinite (Mathlib's `PosSemidef`, which includes symmetry) with non-positive off-diagonal entries; reason: the definition of §2.1.2, p. 3
-- source:
--   Marco Pirazzini, Daniel Spielman, A Fast and Accurate Algorithm for the p → q Norm of Sparse Non-Negative Matrices, STOC 2027 submission #1352 (October 2026), Theorem 10, printed p. 12 (PDF p. 13); proof pp. 12–14; setting §5, p. 12

import Mathlib
import Definitions.Def_PQNormIPM1352_Main_Barrier
import Definitions.Def_PQNormIPM1352_Main_MatrixClasses

open Matrix

namespace PQNormIPM1352.Main

/-- **Theorem 10** (Pirazzini–Spielman, STOC 2027 #1352, p. 12; setting of §5, p. 12). Let
`p ≥ q > 1`, a preprocessed pattern with `s` entries, and `x = (z, y, γ) ∈ int(K)`. Write
`H \ γ = H_w − H_{wγ} H_γ⁻¹ H_{wγ}ᵀ` for the Schur complement of the Hessian of the barrier (6) with
respect to `γ`, `V = (1_m/(1−Z), 0; 0, 1_n/(1−Y)) ∈ ℝ^{(m+n)×2}` and `M = H \ γ − V Vᵀ`, so that
`H \ γ = M + V Vᵀ`. Then `M` is a symmetric M-matrix with at most `4s` non-zero entries, the matrix
`D = Diag(z, y)` has positive diagonal entries, and `D M D` is strictly diagonally dominant. -/
theorem theorem_10 {m n s : ℕ} (P : SparsePattern m n s) (hP : P.Preprocessed) (p q : ℝ)
    (hq : 1 < q) (hqp : q ≤ p) (x : Vec (m + n + s)) (hx : x ∈ interior (P.setK p q)) :
    IsMMatrix (P.schurGamma p q x - P.rank2V x * (P.rank2V x)ᵀ) ∧
      nnz (P.schurGamma p q x - P.rank2V x * (P.rank2V x)ᵀ) ≤ 4 * s ∧
      (∀ u, 0 < P.diagD x u u) ∧
      IsStrictlySDD (P.diagD x * (P.schurGamma p q x - P.rank2V x * (P.rank2V x)ᵀ) * P.diagD x) := by sorry

end PQNormIPM1352.Main
