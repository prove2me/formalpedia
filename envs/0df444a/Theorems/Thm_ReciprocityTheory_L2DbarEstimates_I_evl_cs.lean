-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_evl_cs
-- name    : ReciprocityTheory.L2DbarEstimates.I.evl_cs
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:20.041403+00:00
-- url     : https://prove2.me/theorems/ab2bf6b2-f8f1-44a5-a15f-b62ddd476ef3
-- title:
--   I: evl cs
-- statement:
--   The I construction uses the evl cs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L235-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/EvLeviA.lean#L235-L242

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

theorem ReciprocityTheory.L2DbarEstimates.I.evl_cs {ι : Type*} (s : Finset ι) (u a : ι → ℂ) :
    ‖∑ i ∈ s, conj (u i) * a i‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖ ^ 2) * ∑ i ∈ s, ‖a i‖ ^ 2 := by sorry
