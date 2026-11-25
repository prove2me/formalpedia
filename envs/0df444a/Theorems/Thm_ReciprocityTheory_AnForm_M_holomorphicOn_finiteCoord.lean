-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_holomorphicOn_finiteCoord
-- name    : ReciprocityTheory.AnForm.M.holomorphicOn_finiteCoord
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:24.087573+00:00
-- url     : https://prove2.me/theorems/45fcdf12-0d84-4801-b73d-518672cc0c91
-- title:
--   M: holomorphic On finite Coord
-- statement:
--   The M construction uses the holomorphic On finite Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L261-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ContDiffFubiniStudyRatioCompChart0.lean#L261-L270

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

theorem ReciprocityTheory.AnForm.M.holomorphicOn_finiteCoord : p1.HoloOn (Set.range ((↑) : ℂ → OnePoint ℂ)) crd0 := by sorry
