-- Prove2me | Theorems.Thm_ThreeSum_BruteTripleIndex_decode_code
-- name    : ThreeSum.BruteTripleIndex.decode_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:31.69317+00:00
-- url     : https://prove2.me/theorems/ea09d3fb-3d80-4c69-98a8-64b5685e37a4
-- title:
--   Brute Triple Index: decode code
-- statement:
--   The Brute Triple Index construction uses the decode code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BruteTripleIndex.lean#L31-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/BruteTripleIndex.lean#L31-L46

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_BruteTripleIndex
set_option autoImplicit false
open ThreeSum ThreeSum.BruteTripleIndex

theorem ThreeSum.BruteTripleIndex.decode_code {n : ℕ} (i j k : Fin n) :
    first n (code i j k)=i.val ∧ second n (code i j k)=j.val ∧ third n (code i j k)=k.val := by sorry
