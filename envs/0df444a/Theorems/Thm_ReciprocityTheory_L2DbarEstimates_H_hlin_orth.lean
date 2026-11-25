-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_orth
-- name    : ReciprocityTheory.L2DbarEstimates.H.hlin_orth
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:10:06.227023+00:00
-- url     : https://prove2.me/theorems/3d9cdf96-8ed1-5532-8066-78a9e0e76e3a
-- title:
--   H: hlin orth
-- statement:
--   The H construction uses the hlin orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/HlinVsqPos.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/HlinVsqPos.lean#L57-L66

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
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
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace

theorem ReciprocityTheory.L2DbarEstimates.H.hlin_orth {p : ℕ} (g w : Fin p → ℂ) (hg : g ≠ 0) :
    ∑ j, conj (g j) * perp g w j = 0 := by sorry
