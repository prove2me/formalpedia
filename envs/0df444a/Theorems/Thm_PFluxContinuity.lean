-- Prove2me | Theorems.Thm_PFluxContinuity
-- name    : PFluxContinuity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:10:37.279473+00:00
-- url     : https://prove2.me/theorems/82da9774-da84-426c-8eb0-6c535e79cf33
-- title:
--   PFlux Continuity: PFlux Continuity
-- statement:
--   Norm and continuity of the `p`-flux in the singular range `1 < p < 2`.
--   First, `‖PFlux p ξ‖ = ‖ξ‖ ^ (p - 1)` for EVERY `ξ`, the critical point `ξ = 0`
--   included.  Second, `PFlux p` is continuous on the whole plane.
--
--   Continuity at the origin is the non-obvious half:  for `p < 2` the scalar factor
--   `‖ξ‖ ^ (p - 2)` blows up as `ξ → 0`, and only the cancellation against `ξ` itself
--   keeps the product bounded.  Both uses of the limit passage in the weak equation
--   happen across critical points, so this is exactly what makes them legitimate.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PFluxContinuity.lean#L11-L40
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PFluxContinuity.lean#L11-L40

import Definitions.Def_PHigherOrder_PFlux
import Definitions.Def_PHigherOrder_PFluxContinuity
set_option autoImplicit false

theorem PFluxContinuity (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    (∀ ξ : Plane, ‖PFlux p ξ‖ = ‖ξ‖ ^ (p - 1)) ∧ Continuous (PFlux p) := by sorry
