-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_vsqC
-- name    : ReciprocityTheory.L2DbarEstimates.H.hlin_vsqC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:34.344148+00:00
-- url     : https://prove2.me/theorems/6686c2e7-f526-45c8-aadb-7a889bd9e448
-- title:
--   H: hlin vsq C
-- statement:
--   The H construction uses the hlin vsq C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/HlinVsqPos.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/HlinVsqPos.lean#L11-L13

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

theorem ReciprocityTheory.L2DbarEstimates.H.hlin_vsqC {p : ℕ} (w : Fin p → ℂ) : ((vsq w : ℝ) : ℂ) = ∑ i, w i * conj (w i) := by sorry
