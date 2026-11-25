-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holomorphicOn_infiniteCoord
-- name    : ReciprocityTheory.AnForm.M.holomorphicOn_infiniteCoord
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:06.453482+00:00
-- url     : https://prove2.me/theorems/8bd1d9e2-9e82-4144-b3c8-29eadd495247
-- title:
--   M: holomorphic On infinite Coord
-- statement:
--   The M construction uses the holomorphic On infinite Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L246-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L246-L259

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

theorem ReciprocityTheory.AnForm.M.holomorphicOn_infiniteCoord : p1.HoloOn {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} crd1 := by sorry
