-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_chart
-- name    : ReciprocityTheory.AnForm.M.fsPot_chart
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:41.320468+00:00
-- url     : https://prove2.me/theorems/5b0c873a-d818-54dd-8bae-429ffdd14900
-- title:
--   M: fs Pot chart
-- statement:
--   The M construction uses the fs Pot chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L206-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L206-L236

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology
noncomputable section

theorem ReciprocityTheory.AnForm.M.fsPot_chart (x : OnePoint ℂ) : ∀ j : Fin 2,
    (fsPot.φ x ∘ (p1.chart j).symm = fun w => fubiniStudyProfile (fsQ w)) ∨
      ((fsPot.φ x ∘ (p1.chart j).symm = fun w => fubiniStudyProfileInv (fsQ w)) ∧
        ∀ w ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x, w 0 ≠ 0) := by sorry
