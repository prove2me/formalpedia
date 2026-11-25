-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_fs_local
-- name    : ReciprocityTheory.AnForm.M.fs_local
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:54.443704+00:00
-- url     : https://prove2.me/theorems/70ba7805-7ea5-4198-9133-8448f45c8ac0
-- title:
--   M: fs local
-- statement:
--   The M construction uses the fs local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L303-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L303-L325

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

theorem ReciprocityTheory.AnForm.M.fs_local (ζ0 : ℂ) (h0 : ζ0 ≠ 0) : ∃ W : Set (OnePoint ℂ), IsOpen W ∧
    (ζ0 : OnePoint ℂ) ∈ W ∧ ∃ G : OnePoint ℂ → ℂ, p1.HoloOn W G ∧
      ∀ z ∈ W, ∃ ζ : ℂ, z = ζ ∧ ζ ≠ 0 ∧ (G z).re = Real.log ‖ζ‖ := by sorry
