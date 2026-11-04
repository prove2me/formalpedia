-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_predecessor_bank_or_near
-- name    : ThreeSum.TernaryEuler.predecessor_bank_or_near
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:52.91207+00:00
-- url     : https://prove2.me/theorems/7c9d1276-ae60-4fc8-9c6c-9a6278e9b1f4
-- title:
--   Ternary Euler: predecessor bank or near
-- statement:
--   All positive-coefficient predecessor reads are either bank reads or remain
--   in the same bounded-deficit query neighborhood.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L111-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L111-L123

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.predecessor_bank_or_near {N T : ℕ} {R Q : TritWord N}
    (hRQ : Below R Q) (i : Fin N) :
    predecessor R i ∈ bank N T ∨
      predecessor R i ∈ nearWords Q (rank Q - (T+1)) := by sorry
