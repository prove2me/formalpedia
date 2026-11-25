-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_E_integral_re_double_sum
-- name    : ReciprocityTheory.L2DbarEstimates.E.integral_re_double_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:01:48.875006+00:00
-- url     : https://prove2.me/theorems/30924469-e112-43d6-9a15-d64648a2ac36
-- title:
--   E: integral re double sum
-- statement:
--   The E construction uses the integral re double sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportOfVanish.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/BasicIdentity/HasCompactSupportOfVanish.lean#L14-L23

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_BasicIdentityStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportDTw
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HalfSumNormSubSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_ImportsTer
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_BasicIdentity_HasCompactSupportOfVanish
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.E
open MeasureTheory
open scoped ComplexConjugate
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.E.integral_re_double_sum {M : Type*} [MeasurableSpace M] (μ : Measure M) (n : ℕ)
    (h : Fin n → Fin n → M → ℂ) (hi : ∀ j k, Integrable (h j k) μ) :
    ∫ x, (∑ j, ∑ k, h j k x).re ∂μ = (∑ j, ∑ k, ∫ x, h j k x ∂μ).re := by sorry
