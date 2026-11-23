-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_smoothR_vsq
-- name    : ReciprocityTheory.L2DbarEstimates.H.smoothR_vsq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:16.450538+00:00
-- url     : https://prove2.me/theorems/0a76c8ef-51e9-4c3c-a3cb-f4cff8ac1883
-- title:
--   H: smooth R vsq
-- statement:
--   The H construction uses the smooth R vsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/SmoothRLog.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/SmoothRLog.lean#L19-L30

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

theorem ReciprocityTheory.L2DbarEstimates.H.smoothR_vsq (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) {p : ℕ}
    (g : Fin p → M → ℂ) (hg : ∀ l, Holo n z (g l)) : SmoothR n z (fun x => vsq (gv g x)) := by sorry
