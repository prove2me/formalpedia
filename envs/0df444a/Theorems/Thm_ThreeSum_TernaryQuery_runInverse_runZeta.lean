-- Prove2me | Theorems.Thm_ThreeSum_TernaryQuery_runInverse_runZeta
-- name    : ThreeSum.TernaryQuery.runInverse_runZeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:49.745208+00:00
-- url     : https://prove2.me/theorems/2dc9c5b3-a012-4050-9197-17b5f2e278ad
-- title:
--   Ternary Query: run Inverse run Zeta
-- statement:
--   The Ternary Query construction uses the run Inverse run Zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L66-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L66-L72

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank

theorem ThreeSum.TernaryQuery.runInverse_runZeta {N : ℕ} (coords : List (Fin N)) (f : TritWord N → ℤ) :
    runInverse coords (runZeta coords f) = f := by sorry
