-- Prove2me | Theorems.Thm_ThreeSum_TernaryQuery_update_below
-- name    : ThreeSum.TernaryQuery.update_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:51.049205+00:00
-- url     : https://prove2.me/theorems/9f16df29-238c-4838-92b7-311d8290711f
-- title:
--   Ternary Query: update below
-- statement:
--   The Ternary Query construction uses the update below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L74-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L74-L80

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank

theorem ThreeSum.TernaryQuery.update_below {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d ≤ R i) : Below (Function.update R i d) R := by sorry
