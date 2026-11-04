-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalSpanCatalog_mem_values
-- name    : ThreeSum.TernaryOriginalSpanCatalog.mem_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:33.689661+00:00
-- url     : https://prove2.me/theorems/8794bc05-108d-446b-8dfb-a70f74e2c3a7
-- title:
--   Ternary Original Span Catalog: mem values
-- statement:
--   The Ternary Original Span Catalog construction uses the mem values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpanCatalog.lean#L23-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpanCatalog.lean#L23-L40

import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Theorems.Thm_ThreeSum_TernaryOriginalSpan_mem_values

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpanCatalog
open Finset
set_option maxHeartbeats 2000000
variable {p J : ℕ}

theorem ThreeSum.TernaryOriginalSpanCatalog.mem_values [Fact p.Prime] (rows : List (Fin J → ZMod p)) (v : Fin J → ZMod p) :
    v∈values p rows ↔ v∈Submodule.span (ZMod p) {w | w∈rows} := by sorry
