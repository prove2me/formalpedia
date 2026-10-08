-- Prove2me | Theorems.Thm_SuttonBartoRL_OffPolicy_projection_matrix
-- name    : SuttonBartoRL.OffPolicy.projection_matrix
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:01:23.015291+00:00
-- url     : https://prove2.me/theorems/d753ed94-4de5-4bfb-aff6-210aa1d24f3d
-- title:
--   (11.12)–(11.13) — the projection matrix gives the μ-closest representable value function
-- statement:
--   Let $\mathcal S$ be finite, $\mu$ a probability distribution on $\mathcal S$, $\mathbf D = \operatorname{diag}(\mu)$, and $\mathbf X$ the $|\mathcal S|\times d$ feature matrix, with $\mathbf X^\top\mathbf D\mathbf X$ invertible. Let $\Pi = \mathbf X(\mathbf X^\top\mathbf D\mathbf X)^{-1}\mathbf X^\top\mathbf D$. For every value function $v$:
--
--   1. $\Pi v$ is closest to $v$ among the representable functions: $\|v - \Pi v\|_\mu^2 \le \|v - \mathbf X\mathbf u\|_\mu^2$ for all $\mathbf u\in\mathbb R^d$;
--   2. every minimizer $\mathbf u$ of $\|v - \mathbf X\mathbf u\|_\mu^2$ equals $(\mathbf X^\top\mathbf D\mathbf X)^{-1}\mathbf X^\top\mathbf D v$, and $\mathbf X\mathbf u = \Pi v$, which is definition (11.12);
--   3. $$\Pi^\top\mathbf D\,\Pi = \mathbf D\mathbf X(\mathbf X^\top\mathbf D\mathbf X)^{-1}\mathbf X^\top\mathbf D .$$
--
--   This justifies the matrix formula (11.13) for the projection (11.12), and the identity in 3 is the step from the first to the second form of the PBE in (11.25).
--
--   **Formalization Note** The book substitutes a pseudoinverse when $\mathbf X^\top\mathbf D\mathbf X$ is singular; that case is not formalized. With $\mu > 0$, invertibility is equivalent to linearly independent feature columns.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, (11.12) p. 267; box "The projection matrix", (11.13)–(11.15), p. 268; identity under (11.25), p. 278

import Mathlib
import Definitions.Def_SuttonBartoRL_OffPolicy_LinearGeometry

open Matrix

namespace SuttonBartoRL.OffPolicy

/-- Sutton & Barto (2018), (11.12)–(11.13), pp. 267–268, and the identity quoted under (11.25),
p. 278. Let `µ` be a distribution on the finite state set `S`, `D = diag(µ)`, and `X` the `|S| × d`
feature matrix with `XᵀDX` invertible. Then for every value function `v`:
1. `Πv = X(XᵀDX)⁻¹XᵀDv` is closest to `v` in `‖·‖_µ` among all `v_u = Xu`;
2. every minimizer `u` of `‖v − Xu‖²_µ` equals `(XᵀDX)⁻¹XᵀDv`, so `Xu = Πv` (11.12);
3. `ΠᵀDΠ = DX(XᵀDX)⁻¹XᵀD`. -/
theorem projection_matrix {S : Type} [Fintype S] [DecidableEq S] {d : ℕ}
    (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1)
    (X : Matrix S (Fin d) ℝ) (hX : IsUnit (Xᵀ * Dmat μ * X).det) (v : S → ℝ) :
    (∀ u : Fin d → ℝ, muNormSq μ (v - projMatrix μ X *ᵥ v) ≤ muNormSq μ (v - vw X u)) ∧
    (∀ u : Fin d → ℝ, (∀ u' : Fin d → ℝ, muNormSq μ (v - vw X u) ≤ muNormSq μ (v - vw X u')) →
      u = (Xᵀ * Dmat μ * X)⁻¹ *ᵥ (Xᵀ *ᵥ (Dmat μ *ᵥ v)) ∧ vw X u = projMatrix μ X *ᵥ v) ∧
    (projMatrix μ X)ᵀ * Dmat μ * projMatrix μ X
      = Dmat μ * X * (Xᵀ * Dmat μ * X)⁻¹ * Xᵀ * Dmat μ := by sorry

end SuttonBartoRL.OffPolicy
