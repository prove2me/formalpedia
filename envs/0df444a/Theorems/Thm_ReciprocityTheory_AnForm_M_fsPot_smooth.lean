-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_fsPot_smooth
-- name    : ReciprocityTheory.AnForm.M.fsPot_smooth
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:49.097982+00:00
-- url     : https://prove2.me/theorems/13cb2050-a18e-4aa9-bcbf-c83ff968c694
-- title:
--   M: fs Pot smooth
-- statement:
--   The M construction uses the fs Pot smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L238-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L238-L244

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

theorem ReciprocityTheory.AnForm.M.fsPot_smooth (x : OnePoint ℂ) : p1.SmoothOn (fsPot.U x) (fsPot.φ x) := by sorry
