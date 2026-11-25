-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_projectiveLine_locDens_first_chart
-- name    : ReciprocityTheory.AnForm.M.projectiveLine_locDens_first_chart
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:29:12.08074+00:00
-- url     : https://prove2.me/theorems/1fc5098b-cc42-49af-be92-6038f70ec39f
-- title:
--   M: projective Line loc Dens first chart
-- statement:
--   The M construction uses the projective Line loc Dens first chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProjectiveLinePartitionContinuousCoe.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProjectiveLinePartitionContinuousCoe.lean#L28-L33

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProjectiveLinePartitionContinuousCoe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory OnePoint Filter Topology Set
noncomputable section

theorem ReciprocityTheory.AnForm.M.projectiveLine_locDens_first_chart (y : Fin 1 → ℂ) : locDens p1 (fun _ => fsPot) p1i0 y = fsDens (y 0) := by sorry
