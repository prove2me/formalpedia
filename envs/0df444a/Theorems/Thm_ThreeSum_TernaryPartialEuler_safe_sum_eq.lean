-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_safe_sum_eq
-- name    : ThreeSum.TernaryPartialEuler.safe_sum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:31.471757+00:00
-- url     : https://prove2.me/theorems/6a8182c6-1e09-474a-9695-1411066da2e4
-- title:
--   Ternary Partial Euler: safe sum eq
-- statement:
--   The Ternary Partial Euler construction uses the safe sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L102-L117
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L102-L117

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.safe_sum_eq {N : ℕ} (S : Finset (Fin N)) (R dummy : TritWord N)
    (F : TritWord N→ℤ) :
    (∑ i : Fin N, restrictedWeight S R i*F (safePredecessor S R dummy i))=
      ∑ i∈S, (R i).val*F (predecessor R i) := by sorry
