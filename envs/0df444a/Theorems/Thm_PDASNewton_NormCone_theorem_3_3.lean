-- Prove2me | Theorems.Thm_PDASNewton_NormCone_theorem_3_3
-- name    : PDASNewton.NormCone.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:29.153196+00:00
-- url     : https://prove2.me/theorems/d5e5dc9f-ecbe-4629-bd6e-ce56fe509048
-- title:
--   Theorem 3.3, p. 8 — for a P-matrix with ‖(A_𝓘⁻¹A_𝓘𝓐)₊‖₁ < 1 and Σ_𝓘(A_𝓘⁻¹y_𝓘)ᵢ ≥ 0 for y_𝓘 ≥ 0, xᵏ → x* from arbitrary initial data
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a P-matrix (every principal minor is positive), $f, \psi \in \mathbb{R}^n$ and $c > 0$. Assume that for every partition of $\{1,\dots,n\}$ into disjoint sets $\mathcal{I}$ and $\mathcal{A}$ (the trivial partitions included)
--
--   1. $\|(A_{\mathcal{I}}^{-1}A_{\mathcal{I}\mathcal{A}})_+\|_1 < 1$, where $B_+$ is the matrix of positive parts of the entries of $B$ and $\|\cdot\|_1$ is the matrix norm subordinate to the one-norms (maximal column sum);
--   2. $\sum_{i\in\mathcal{I}} (A_{\mathcal{I}}^{-1} v)_i \ge 0$ for every $v \in \mathbb{R}^{|\mathcal{I}|}$ with $v \ge 0$.
--
--   Here $A_{\mathcal{I}}$ is the principal submatrix of $A$ on $\mathcal{I}$ and $A_{\mathcal{I}\mathcal{A}}$ the submatrix with rows in $\mathcal{I}$ and columns in $\mathcal{A}$ (calligraphic $\mathcal{A}$, $\mathcal{I}$ are index sets; $A$ is the matrix). Let $x^* = (y^*, \lambda^*)$ solve
--   $$Ay + \lambda = f, \qquad \lambda - \max(0, \lambda + c(y - \psi)) = 0, \tag{3.1}$$
--   and let $x^k = (y^k, \lambda^k)$, $k \ge 0$, be the iterates of the primal-dual active set algorithm from arbitrary initial data $(y^0, \lambda^0)$. Then
--   $$\lim_{k\to\infty} x^k = x^*.$$
--
--   This is a global convergence result for the primal-dual active set strategy beyond the M-matrix case of Theorem 3.2: the sum $\sum_i y^k_i$ serves as a merit function. Remark 3.3 notes that M-matrices satisfy both conditions.
--
--   **Formalization Note** The solution $(y^*, \lambda^*)$ is a hypothesis; for a P-matrix (3.1) has exactly one solution, so nothing is assumed beyond the paper. Both conditions are quantified over every `S : Finset (Fin n)` with $\mathcal{I} = S$, $\mathcal{A} = S^c$; the norm of a matrix with no columns ($\mathcal{A} = \emptyset$) is $0$. The inverses are genuine because a P-matrix has nonsingular principal submatrices. Convergence is in the product topology of $\mathbb{R}^n \times \mathbb{R}^n$. A run is any sequence satisfying steps (ii)–(iii) at every $k$; the stopping option (iv) is not modelled.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 8, Theorem 3.3

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting
import Definitions.Def_PDASNewton_NormCone_Setting

open Filter Topology Matrix

namespace PDASNewton.NormCone

theorem theorem_3_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : RobinsonSR.Schur.IsPMatrix A)
    (hnorm : ∀ S : Finset (Fin n), posPartOneNorm ((PDASNewton.MMatrix.principal A S)⁻¹ * PDASNewton.MMatrix.offDiag A S) < 1)
    (hcone : ∀ S : Finset (Fin n), ∀ v : S → ℝ, 0 ≤ v → 0 ≤ ∑ i, ((PDASNewton.MMatrix.principal A S)⁻¹ *ᵥ v) i)
    (ystar lamstar : Fin n → ℝ) (hsol : PDASNewton.Local.IsSolution A f ψ c ystar lamstar)
    (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    Tendsto (fun k => (y k, lam k)) atTop (𝓝 (ystar, lamstar)) := by sorry

end PDASNewton.NormCone
