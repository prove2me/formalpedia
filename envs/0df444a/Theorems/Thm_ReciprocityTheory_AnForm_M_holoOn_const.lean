-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holoOn_const
-- name    : ReciprocityTheory.AnForm.M.holoOn_const
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:22:35.197587+00:00
-- url     : https://prove2.me/theorems/28354779-3852-58df-b1ac-e43994a9abdb
-- title:
--   M: holo On const
-- statement:
--   The M construction uses the holo On const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L277-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L277-L279

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

theorem ReciprocityTheory.AnForm.M.holoOn_const (U : Set (OnePoint ℂ)) (c : ℂ) : p1.HoloOn U (fun _ => c) := by sorry
