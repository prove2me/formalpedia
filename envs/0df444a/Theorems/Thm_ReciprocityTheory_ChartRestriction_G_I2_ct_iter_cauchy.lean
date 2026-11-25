-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_cauchy
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cauchy
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:22.328713+00:00
-- url     : https://prove2.me/theorems/a64daf42-5389-5905-8e04-924a738e7177
-- title:
--   I2: ct iter cauchy
-- statement:
--   The I2 construction uses the ct iter cauchy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L8-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L8-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Metric

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_iter_cauchy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (F : V → ℂ) (hF : ∀ m : ℕ, ContDiff ℂ m F) (ρ M : ℝ) (hρ : 0 < ρ) :
    ∀ (k : ℕ) (x : Fin k → V) (x₀ : V), (∀ j, ‖x j‖ ≤ 1) →
    (∀ y, ‖y - x₀‖ ≤ k * ρ → ‖F y‖ ≤ M) →
    ‖iteratedFDeriv ℂ k F x₀ x‖ ≤ M / ρ ^ k
  := by sorry
