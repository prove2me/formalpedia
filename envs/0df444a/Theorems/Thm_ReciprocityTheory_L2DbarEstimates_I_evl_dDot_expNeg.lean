-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_expNeg
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_dDot_expNeg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:04:21.469034+00:00
-- url     : https://prove2.me/theorems/2633e3be-b069-4ba2-9ce2-5f73fc31d5be
-- title:
--   I: evl d Dot exp Neg
-- statement:
--   The I construction uses the evl d Dot exp Neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L150-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L150-L162

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.evl_dDot_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (hph : SmoothR n z ph) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => ((Real.exp (-ph y) : ℝ) : ℂ)) x ξ =
      -((Real.exp (-ph x) : ℝ) : ℂ) * dDot n z (fun y => (ph y : ℂ)) x ξ := by sorry
