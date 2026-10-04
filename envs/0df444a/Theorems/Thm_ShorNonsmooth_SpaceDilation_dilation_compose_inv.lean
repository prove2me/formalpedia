-- Prove2me | Theorems.Thm_ShorNonsmooth_SpaceDilation_dilation_compose_inv
-- name    : ShorNonsmooth.SpaceDilation.dilation_compose_inv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T23:53:40.545716+00:00
-- url     : https://prove2.me/theorems/09a91015-f15d-4fe8-b06c-61cff05c2a39
-- title:
--   $R_a(\xi) \circ R_{1/a}(\xi) = \mathrm{id}$ for a unit vector $\xi$ (Shor 1985, p. 50, (3.3))
-- statement:
--   Write `x = (x, ξ) ξ + w` with `w ⟂ ξ`. Then `R_a(ξ) x = a (x, ξ) ξ + w` and `R_{1/a}(ξ) (a (x, ξ) ξ + w) = (1/a) a (x, ξ) ξ + w = (x, ξ) ξ + w = x`, so `R_a(ξ) R_{1/a}(ξ) = id`.
--
--   This is the algebraic identity underlying the SDG recursion (3.9): with `B k+1 = B k R_{1/α k+1}(ξ k+1)` and `A k+1 = R_{α k+1}(ξ k+1) A k` the two operators stay inverse to each other at every step, starting from `A 0 = B 0 = id`. It is what allows the transformed gradient `g̃ k = B k* g(x k)` to be rewritten as `g̃ k = A k⁻¹ g(x k)`, the form used throughout the proof of Theorem 3.2.
--
--   The statement is stated at the level of continuous linear maps on `E n`, matching the `dilation` definition, and requires only `a ≠ 0` together with `‖ξ‖ = 1`.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 50, (3.3) and formulas (3.9)

import Mathlib
import Definitions.Def_ShorNonsmooth_SpaceDilation_SDGMethod

namespace ShorNonsmooth.SpaceDilation

/-- The operator of space dilation along `ξ` with coefficient `a` and the one with
coefficient `1/a` are mutual inverses along the same direction, for a nonzero `a` and a
unit vector `ξ`: `R_a(ξ) ∘ R_{1/a}(ξ) = id`. This is the algebraic fact that makes
`B k = R_{1/α_k}(ξ k) ⋯ R_{1/α_1}(ξ 1) B 0` the inverse of
`A k = R_{α_k}(ξ k) ⋯ R_{α_1}(ξ 1) A 0`, i.e. `A k ∘ B k = id`. -/
theorem dilation_compose_inv {n : ℕ} (a : ℝ) (ha : a ≠ 0) (ξ : EuclideanSpace ℝ (Fin n))
    (hξ : ‖ξ‖ = 1) : dilation a ξ ∘ dilation (1 / a) ξ = ContinuousLinearMap.id ℝ _ := by
  sorry

end ShorNonsmooth.SpaceDilation
