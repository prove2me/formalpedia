-- Prove2me | Theorems.Thm_SuttonBartoRL_LinearTD_posDef_unique_solution
-- name    : SuttonBartoRL.LinearTD.posDef_unique_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:48:19.571031+00:00
-- url     : https://prove2.me/theorems/e6325cba-315b-46ba-a5d6-344eefe85470
-- title:
--   A positive definite $\mathbf A$ is invertible and $\mathbf w = \mathbf A^{-1}\mathbf b$ is the unique solution of $\mathbf b = \mathbf A\mathbf w$
-- statement:
--   Let $\mathbf A$ be a real $d \times d$ matrix, not necessarily symmetric, that is positive definite in the sense $y^\top \mathbf A y > 0$ for every $y \ne 0$, and let $\mathbf b \in \mathbb R^d$. Then
--
--   1. $\mathbf A$ is invertible;
--   2. $\mathbf w_{\mathrm{TD}} = \mathbf A^{-1}\mathbf b$ satisfies $\mathbf b = \mathbf A \mathbf w_{\mathrm{TD}}$;
--   3. every $\mathbf w$ with $\mathbf b = \mathbf A \mathbf w$ equals $\mathbf A^{-1}\mathbf b$.
--
--   $$\mathbf b - \mathbf A\mathbf w = \mathbf 0 \iff \mathbf w = \mathbf A^{-1}\mathbf b .$$
--
--   Applied to the $\mathbf A$ and $\mathbf b$ of (9.11), this is the existence and uniqueness of the TD fixed point (9.12), the only possible limit of linear semi-gradient TD(0).
--
--   **Formalization Note** Positive definiteness is in the book's sense for non-symmetric matrices, not Mathlib's `Matrix.PosDef`. Lean's matrix inverse is the zero matrix for a singular matrix, so conclusion 1 is what makes $\mathbf A^{-1}$ the genuine inverse.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eq. (9.12) and box "Proof of Convergence of Linear TD(0)", p. 206

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

namespace SuttonBartoRL.LinearTD

/-- Sutton & Barto (2018), (9.12) and box, p. 206: "Positive definiteness also ensures that the
inverse `A⁻¹` exists." If `A` is positive definite (`yᵀAy > 0` for `y ≠ 0`, `A` not necessarily
symmetric), then `A` is invertible, `w = A⁻¹b` solves `b = Aw`, and it is the only solution. -/
theorem posDef_unique_solution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ)
    (hA : IsPosDefNonsym A) :
    IsUnit A.det ∧ A *ᵥ (A⁻¹ *ᵥ b) = b ∧ ∀ w : Fin d → ℝ, A *ᵥ w = b → w = A⁻¹ *ᵥ b := by sorry

end SuttonBartoRL.LinearTD
