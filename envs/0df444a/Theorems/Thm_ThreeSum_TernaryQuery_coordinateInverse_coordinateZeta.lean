-- Prove2me | Theorems.Thm_ThreeSum_TernaryQuery_coordinateInverse_coordinateZeta
-- name    : ThreeSum.TernaryQuery.coordinateInverse_coordinateZeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:50.684685+00:00
-- url     : https://prove2.me/theorems/4f0962aa-3dc4-415a-bc94-e44783465151
-- title:
--   Ternary Query: coordinate Inverse coordinate Zeta
-- statement:
--   The Ternary Query construction uses the coordinate Inverse coordinate Zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L42-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L42-L48

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank

theorem ThreeSum.TernaryQuery.coordinateInverse_coordinateZeta {N : ℕ} (i : Fin N)
    (f : TritWord N → ℤ) : coordinateInverse i (coordinateZeta i f) = f := by sorry
