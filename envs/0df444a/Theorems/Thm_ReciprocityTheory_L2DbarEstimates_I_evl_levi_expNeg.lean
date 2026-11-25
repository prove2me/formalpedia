-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_levi_expNeg
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_levi_expNeg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:58:50.928743+00:00
-- url     : https://prove2.me/theorems/b93253e5-dd4b-4631-bbd6-e4480705e364
-- title:
--   I: evl levi exp Neg
-- statement:
--   The I construction uses the evl levi exp Neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L164-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L164-L202

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj

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

theorem ReciprocityTheory.L2DbarEstimates.I.evl_levi_expNeg {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (ph : M → ℝ)
    (hph : SmoothR n z ph) (x : M) (ξ : Fin n → ℂ) :
    Levi n z (fun y => Real.exp (-ph y)) x ξ =
      ((Real.exp (-ph x) : ℝ) : ℂ) * (dDot n z (fun y => (ph y : ℂ)) x ξ *
        conj (dDot n z (fun y => (ph y : ℂ)) x ξ) - Levi n z ph x ξ) := by sorry
