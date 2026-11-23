-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_vsq_pos
-- name    : ReciprocityTheory.L2DbarEstimates.H.vsq_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:42:30.230865+00:00
-- url     : https://prove2.me/theorems/d96030ba-e5b9-4ac4-ad86-4dcd7864b150
-- title:
--   H: vsq pos
-- statement:
--   The H construction uses the vsq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/SmoothRLog.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/SmoothRLog.lean#L9-L17

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SmoothRLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace ContDiff

theorem ReciprocityTheory.L2DbarEstimates.H.vsq_pos {p : ℕ} (w : Fin p → ℂ) (hw : w ≠ 0) : 0 < vsq w := by sorry
