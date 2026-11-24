-- Prove2me | Theorems.Thm_ValiantBorder_contractingCuts
-- name    : ValiantBorder.contractingCuts
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:34:39.301831+00:00
-- url     : https://prove2.me/theorems/2b494e22-ad50-4cac-a691-65bc264f81f3
-- title:
--   Contracting fields admit scale cuts
-- statement:
--   For every contracting field there is a subring finitely generated over the integers and a finitely supported choice of weights such that cut programs exist at all sufficiently large allowed scales. The scale parameter has the form $16h$ with $h≥17$.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Scales.lean#L121-L140).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Scales.lean#L121-L140.

import Definitions.Def_ValiantBorder_scaleCuts
import Definitions.Def_ValiantBorder_fieldCases

theorem ValiantBorder.contractingCuts {K : Type} [Field K] (hK : Paper.Contracting K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (θ : List Bool → A) (h C₀ v₀ : ℕ),
      (Function.support θ).Finite ∧ 17 ≤ h ∧ NS1.CutHyp θ (16 * h) C₀ v₀ := by sorry
