-- Prove2me | Theorems.Thm_ThreeSum_TernaryQuery_coordinate_read_in_bank
-- name    : ThreeSum.TernaryQuery.coordinate_read_in_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:52.999808+00:00
-- url     : https://prove2.me/theorems/704c9805-8b34-48de-8184-ed2098cab995
-- title:
--   Ternary Query: coordinate read in bank
-- statement:
--   Every read of one compressed coordinate stage stays in the rank bank.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L83-L86
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L83-L86

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank

theorem ThreeSum.TernaryQuery.coordinate_read_in_bank {N T : ℕ} {R : TritWord N} (hR : R ∈ bank N T)
    (i : Fin N) (d : Fin 3) (hd : d ≤ R i) :
    Function.update R i d ∈ bank N T := by sorry
