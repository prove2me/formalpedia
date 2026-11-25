-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holomorphicOn_comp_finiteCoord
-- name    : ReciprocityTheory.AnForm.M.holomorphicOn_comp_finiteCoord
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:11.168377+00:00
-- url     : https://prove2.me/theorems/16fe2ce1-b996-4c23-a58d-e5aa5d4f8343
-- title:
--   M: holomorphic On comp finite Coord
-- statement:
--   The M construction uses the holomorphic On comp finite Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L281-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L281-L301

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

theorem ReciprocityTheory.AnForm.M.holomorphicOn_comp_finiteCoord {B : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F B) :
    p1.HoloOn (projectiveLineChartAtZero.source ∩ projectiveLineChartAtZero ⁻¹' {w | w 0 ∈ B}) (fun x => F (crd0 x)) := by sorry
