-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalSpan_values_length
-- name    : ThreeSum.TernaryOriginalSpan.values_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:19.516204+00:00
-- url     : https://prove2.me/theorems/7998c24f-f202-4e84-9621-1654b5a94f66
-- title:
--   Ternary Original Span: values length
-- statement:
--   The Ternary Original Span construction uses the values length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpan.lean#L18-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpan.lean#L18-L23

import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpan
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V]

theorem ThreeSum.TernaryOriginalSpan.values_length (rows : List V) : (values K rows).length = Fintype.card K^rows.length := by sorry
