-- Prove2me | Theorems.Thm_RobustLS_Unstructured_rank_one_worst_case_perturbation
-- name    : RobustLS.Unstructured.rank_one_worst_case_perturbation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:25:23.784034+00:00
-- url     : https://prove2.me/theorems/5f9ca8c1-18a0-4413-a81c-23a5713df012
-- title:
--   Theorem 3.1, proof — a rank-one perturbation of norm 1 attains ‖Ax − b‖ + √(‖x‖² + 1) (sign corrected)
-- statement:
--   Let $A \in \mathbb{R}^{n\times m}$, $b \in \mathbb{R}^n$, $x \in \mathbb{R}^m$, and let $u \in \mathbb{R}^n$ be a unit vector with $u = (Ax-b)/\|Ax-b\|$ whenever $Ax \ne b$. Define the rank-one perturbation
--
--   $$
--   [\Delta A\ \ \Delta b] = \frac{u}{\sqrt{\|x\|^2+1}}\,\bigl[\,x^T\ \ {-1}\,\bigr],
--   \qquad\text{i.e.}\quad \Delta A = \frac{u x^T}{\sqrt{\|x\|^2+1}},\quad \Delta b = -\frac{u}{\sqrt{\|x\|^2+1}} .
--   $$
--
--   Then $\|[\Delta A\ \Delta b]\|_F = \|[\Delta A\ \Delta b]\| = 1$ (Frobenius norm and largest singular value), and
--
--   $$
--   \|(A+\Delta A)x - (b+\Delta b)\| = \|Ax-b\| + \sqrt{\|x\|^2+1}.
--   $$
--
--   Together with the upper bound (16) this shows that the bound is attained, for both the Frobenius and the largest-singular-value perturbation balls.
--
--   **Correction of the printed statement.** The paper prints $[x^T\ \ 1]$ in place of $[x^T\ \ {-1}]$. With the printed sign the residual becomes $Ax - b + u(\|x\|^2-1)/\sqrt{\|x\|^2+1}$, which does not attain the bound: for $A = 0$, $x = 0$, $b = e_1$ one gets $u = -e_1$, $\Delta A = 0$, $\Delta b = -e_1$ and residual $0$, while $\|Ax-b\|+\sqrt{\|x\|^2+1} = 2$. The corrected sign is the one the paper's claimed equality requires.
--
--   **Formalization Note** The augmented matrix is indexed by `Fin m ⊕ Unit`; the norms are the explicit Euclidean, Frobenius and operator-norm definitions of the mission's definition module.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1040, Theorem 3.1, proof (worst-case perturbation; sign of the last column corrected)

import Mathlib
import Definitions.Def_RobustLS_Unstructured_Core

open Matrix

namespace RobustLS.Unstructured

/-- El Ghaoui & Lebret (1997), Theorem 3.1, proof, p. 1040 (PDF p. 6): the rank-one worst-case
perturbation `Δ = u/√(‖x‖² + 1) · [xᵀ  −1]`, where `u = (Ax − b)/‖Ax − b‖` if `Ax ≠ b` and
`u` is any unit vector otherwise, satisfies `‖Δ‖_F = ‖Δ‖ = 1` and
`‖(A + ΔA)x − (b + Δb)‖ = ‖Ax − b‖ + √(‖x‖² + 1)`.
**Correction of a printed sign:** the paper prints `[xᵀ 1]`; with that choice the residual is
`Ax − b + u(‖x‖² − 1)/√(‖x‖² + 1)`, which does not attain the bound (e.g. `A = 0`, `x = 0`,
`b = e₁`: residual `0` instead of `2`). The last column must be `−u/√(‖x‖² + 1)`. -/
theorem rank_one_worst_case_perturbation {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) (u : Fin n → ℝ) (hu : eucNorm u = 1)
    (hu_dir : A *ᵥ x ≠ b → u = (eucNorm (A *ᵥ x - b))⁻¹ • (A *ᵥ x - b)) :
    let c : ℝ := (Real.sqrt (eucNorm x ^ 2 + 1))⁻¹
    let ΔA : Matrix (Fin n) (Fin m) ℝ := c • Matrix.vecMulVec u x
    let Δb : Fin n → ℝ := (-c) • u
    frobNorm (augment ΔA Δb) = 1 ∧ specNorm (augment ΔA Δb) = 1 ∧
      perturbedResidual A b ΔA Δb x = eucNorm (A *ᵥ x - b) + Real.sqrt (eucNorm x ^ 2 + 1) := by sorry

end RobustLS.Unstructured
