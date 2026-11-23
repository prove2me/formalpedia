-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_vsq_pos
-- name    : ReciprocityTheory.L2DbarEstimates.H.hlin_vsq_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:10.344568+00:00
-- url     : https://prove2.me/theorems/6822be43-50a5-405a-a7c7-6d873cb74b98
-- title:
--   H: hlin vsq pos
-- statement:
--   The H construction uses the hlin vsq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/HlinVsqPos.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/HlinVsqPos.lean#L15-L18

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
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

theorem ReciprocityTheory.L2DbarEstimates.H.hlin_vsq_pos {p : ℕ} {g : Fin p → ℂ} (hg : g ≠ 0) : 0 < vsq g := by sorry
