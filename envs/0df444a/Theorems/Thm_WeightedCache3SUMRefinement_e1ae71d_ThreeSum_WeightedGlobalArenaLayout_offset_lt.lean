-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaLayout_offset_lt
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout.offset_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T11:22:38.991693+00:00
-- url     : https://prove2.me/theorems/3a949edd-5218-4844-ab0b-9bc45a0b2aaf
-- title:
--   offset_lt
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaLayout.lean#L105-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaLayout.lean#L105-L108

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLayout
import Theorems.Thm_ThreeSum_LightBalancedOffset_offset_lt

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaLayout.offset_lt {free C slot len offset : ℕ} (hoff : offset<len) (hlen : len≤C) :
    addr free C slot+offset<addr free C (slot+1) := by sorry
