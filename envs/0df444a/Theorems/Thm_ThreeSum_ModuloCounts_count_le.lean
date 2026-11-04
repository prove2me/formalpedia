-- Prove2me | Theorems.Thm_ThreeSum_ModuloCounts_count_le
-- name    : ThreeSum.ModuloCounts.count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:33:44.775558+00:00
-- url     : https://prove2.me/theorems/d0acfd2c-ef1f-42c5-9b57-1c9d53431a73
-- title:
--   Modulo Counts: count le
-- statement:
--   The Modulo Counts construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean#L51-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ModuloCounts.lean#L51-L62

import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_ModuloCounts
import Theorems.Thm_ThreeSum_LightHistogram_count_le

set_option autoImplicit false
open ThreeSum ThreeSum.ModuloCounts
open Finset LightResidueHistogram
open scoped BigOperators

theorem ThreeSum.ModuloCounts.count_le (p nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c ≤ nA*nB*nC := by sorry
