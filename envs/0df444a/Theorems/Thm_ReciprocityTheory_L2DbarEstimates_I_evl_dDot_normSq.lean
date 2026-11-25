-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_dDot_normSq
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_dDot_normSq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:59:42.441298+00:00
-- url     : https://prove2.me/theorems/ac5af113-82ef-5b02-bd24-5cad8d60fd86
-- title:
--   I: evl d Dot norm Sq
-- statement:
--   The I construction uses the evl d Dot norm Sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L89-L100

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

theorem ReciprocityTheory.L2DbarEstimates.I.evl_dDot_normSq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : M → ℂ)
    (hg : Holo n z g) (x : M) (ξ : Fin n → ℂ) :
    dDot n z (fun y => ((‖g y‖ ^ 2 : ℝ) : ℂ)) x ξ = conj (g x) * dDot n z g x ξ := by sorry
