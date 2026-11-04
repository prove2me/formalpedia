-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalSpanCatalog_representative_axpy
-- name    : ThreeSum.TernaryOriginalSpanCatalog.representative_axpy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:18.741375+00:00
-- url     : https://prove2.me/theorems/4fa0eabb-0e23-479b-9924-0e3b9a35d3b2
-- title:
--   Ternary Original Span Catalog: representative axpy
-- statement:
--   The Ternary Original Span Catalog construction uses the representative axpy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpanCatalog.lean#L42-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpanCatalog.lean#L42-L47

import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpanCatalog
open Finset
set_option maxHeartbeats 2000000
variable {p J : ℕ}

theorem ThreeSum.TernaryOriginalSpanCatalog.representative_axpy [NeZero p] (a : ℕ) (row old : Fin J → ZMod p) (i : Fin J) :
    (((a : ZMod p) • row+old) i).val=((old i).val+a*(row i).val)%p := by sorry
