-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalSpan_mem_values
-- name    : ThreeSum.TernaryOriginalSpan.mem_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:22.733474+00:00
-- url     : https://prove2.me/theorems/98d58f42-39e4-425e-8ab3-97cbc48f6287
-- title:
--   Ternary Original Span: mem values
-- statement:
--   The Ternary Original Span construction uses the mem values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpan.lean#L25-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpan.lean#L25-L42

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpan
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]

theorem ThreeSum.TernaryOriginalSpan.mem_values (rows : List V) (v : V) :
    v ∈ values K rows ↔ v ∈ Submodule.span K {w | w ∈ rows} := by sorry
