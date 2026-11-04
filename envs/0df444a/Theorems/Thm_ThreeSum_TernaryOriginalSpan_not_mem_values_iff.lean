-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalSpan_not_mem_values_iff
-- name    : ThreeSum.TernaryOriginalSpan.not_mem_values_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:17.248219+00:00
-- url     : https://prove2.me/theorems/96407678-2e02-472f-9941-6e4776955ba6
-- title:
--   Ternary Original Span: not mem values iff
-- statement:
--   The Ternary Original Span construction uses the not mem values iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpan.lean#L44-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpan.lean#L44-L46

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpan
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]

theorem ThreeSum.TernaryOriginalSpan.not_mem_values_iff (rows : List V) (v : V) :
    v ∉ values K rows ↔ v ∉ Submodule.span K {w | w ∈ rows} := by sorry
