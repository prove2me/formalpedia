-- Prove2me | Theorems.Thm_ThreeSum_TernaryOriginalSpanCatalog_values_length
-- name    : ThreeSum.TernaryOriginalSpanCatalog.values_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:31.59664+00:00
-- url     : https://prove2.me/theorems/9fd5d42c-5b87-469f-b2d9-3e1e1887995c
-- title:
--   Ternary Original Span Catalog: values length
-- statement:
--   The Ternary Original Span Catalog construction uses the values length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpanCatalog.lean#L16-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryOriginalSpanCatalog.lean#L16-L21

import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpan
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Theorems.Thm_ThreeSum_TernaryOriginalSpan_values_length

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalSpanCatalog
open Finset
set_option maxHeartbeats 2000000
variable {p J : ℕ}

theorem ThreeSum.TernaryOriginalSpanCatalog.values_length (rows : List (Fin J → ZMod p)) : (values p rows).length=p^rows.length := by sorry
