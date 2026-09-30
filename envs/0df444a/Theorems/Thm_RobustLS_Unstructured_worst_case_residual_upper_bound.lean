-- Prove2me | Theorems.Thm_RobustLS_Unstructured_worst_case_residual_upper_bound
-- name    : RobustLS.Unstructured.worst_case_residual_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:24:54.280517+00:00
-- url     : https://prove2.me/theorems/9ecc2f90-80a9-40b4-895a-11233582e52f
-- title:
--   §3.1, Eq. (16) — the worst-case residual is at most ‖Ax − b‖ + √(‖x‖² + 1)
-- statement:
--   Let $A \in \mathbb{R}^{n\times m}$, $b \in \mathbb{R}^n$ and $x \in \mathbb{R}^m$, with Euclidean norms on vectors. For every perturbation $\Delta A \in \mathbb{R}^{n\times m}$, $\Delta b \in \mathbb{R}^n$ whose augmented matrix has Frobenius norm $\|[\Delta A\ \Delta b]\|_F \le 1$,
--
--   $$
--   \|(A+\Delta A)x - (b+\Delta b)\| \le \|Ax - b\| + \sqrt{\|x\|^2 + 1}.
--   $$
--
--   Taking the maximum over all such perturbations gives the upper bound (16), $r(A,b,x) \le \|Ax-b\| + \sqrt{\|x\|^2+1}$, the first half of the closed form in Theorem 3.1.
--
--   **Formalization Note** The bound is stated perturbation by perturbation rather than for the `sSup` defining $r$, so that it cannot hold for the vacuous reason that a supremum of an unbounded set is $0$ in Lean. The paper normalizes $\rho = 1$.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1040, Theorem 3.1, proof, Eq. (16)

import Mathlib
import Definitions.Def_RobustLS_Unstructured_Core

open Matrix

namespace RobustLS.Unstructured

/-- El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.1, proof, Eq. (16), p. 1040 (PDF p. 6):
`r(A, b, x) ≤ ‖Ax − b‖ + √(‖x‖² + 1)` (with `ρ = 1`). Stated perturbation by perturbation:
every `[ΔA Δb]` with Frobenius norm at most `1` gives a residual at most the bound. -/
theorem worst_case_residual_upper_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) (ΔA : Matrix (Fin n) (Fin m) ℝ) (Δb : Fin n → ℝ)
    (hΔ : frobNorm (augment ΔA Δb) ≤ 1) :
    perturbedResidual A b ΔA Δb x ≤ eucNorm (A *ᵥ x - b) + Real.sqrt (eucNorm x ^ 2 + 1) := by sorry

end RobustLS.Unstructured
