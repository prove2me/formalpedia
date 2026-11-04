-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceLayout_geometry
-- name    : ThreeSum.WeightedGlobalArenaSourceLayout.geometry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:44:14.686653+00:00
-- url     : https://prove2.me/theorems/43acb24b-ec40-410e-b109-ab6f2b657ff7
-- title:
--   Weighted Global Arena Source Layout: geometry
-- statement:
--   All three actual Cartesian dictionaries, the actual residue join and
--   the grouped weighted histogram fit distinct literal arena slots.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceLayout.lean#L58-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceLayout.lean#L58-L83

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalArenaSourceLayout
open WeightedGlobalArenaLayout TernarySourceExecutionFactory LightTernarySourceHost

theorem ThreeSum.WeightedGlobalArenaSourceLayout.geometry {free C start space : ℕ} (S : Setup)
    (hs : start=30 ∨ start=39) (hend : finish free C≤space)
    (hlocal : S.xs.length≤C) (hradix : LightRadixKeys.space 0 S.xs.length S.J≤C)
    (hjoin : LightWantedSetup.space 0 S.M S.input (dictionary S.xs S.p0 S.J)
      S.NL (size S.xs S.J) S.U 0 0≤C)
    (hhits : count S.xs S.p0 S.J S.M S.NL S.input≤C)
    (hvalues : S.groups*S.bank≤C) : Geometry (setup S free C start) space := by sorry
