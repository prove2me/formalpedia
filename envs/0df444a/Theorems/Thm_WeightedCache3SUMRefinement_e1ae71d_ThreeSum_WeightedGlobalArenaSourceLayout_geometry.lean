-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceLayout_geometry
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceLayout.geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:30:42.871827+00:00
-- url     : https://prove2.me/theorems/e3da708f-cd8c-40c1-a7fd-51d422336c2b
-- title:
--   geometry
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceLayout.lean#L58-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceLayout.lean#L58-L83

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceLayout
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceLayout
open WeightedGlobalArenaLayout TernarySourceExecutionFactory LightTernarySourceHost

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceLayout.geometry {free C start space : ℕ} (S : Setup)
    (hs : start=30 ∨ start=39) (hend : finish free C≤space)
    (hlocal : S.xs.length≤C) (hradix : LightRadixKeys.space 0 S.xs.length S.J≤C)
    (hjoin : LightWantedSetup.space 0 S.M S.input (dictionary S.xs S.p0 S.J)
      S.NL (size S.xs S.J) S.U 0 0≤C)
    (hhits : count S.xs S.p0 S.J S.M S.NL S.input≤C)
    (hvalues : S.groups*S.bank≤C) : Geometry (setup S free C start) space := by sorry
