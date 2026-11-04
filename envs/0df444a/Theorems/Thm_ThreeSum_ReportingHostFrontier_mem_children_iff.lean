-- Prove2me | Theorems.Thm_ThreeSum_ReportingHostFrontier_mem_children_iff
-- name    : ThreeSum.ReportingHostFrontier.mem_children_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:31:55.44322+00:00
-- url     : https://prove2.me/theorems/bf028d0f-a719-48d8-8157-9df875ff38e4
-- title:
--   Reporting Host Frontier: mem children iff
-- statement:
--   The Reporting Host Frontier construction uses the mem children iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L20-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostFrontier.lean#L20-L25

import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Definitions.Def_Submission_ThreeSum_ReportingHostFrontier
set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostFrontier
open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators

theorem ThreeSum.ReportingHostFrontier.mem_children_iff {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (S : Finset (Fin (512*h))) : S ∈ children q k ↔ S ∈ RawReporting.children q k := by sorry
