-- Prove2me | Theorems.Thm_ThreeSum_TernaryQuery_coordinateZeta_coordinateInverse
-- name    : ThreeSum.TernaryQuery.coordinateZeta_coordinateInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:50.621437+00:00
-- url     : https://prove2.me/theorems/dca35955-ebda-41c9-bb50-d8e020a7cbee
-- title:
--   Ternary Query: coordinate Zeta coordinate Inverse
-- statement:
--   The Ternary Query construction uses the coordinate Zeta coordinate Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L50-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryQuery.lean#L50-L56

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank

theorem ThreeSum.TernaryQuery.coordinateZeta_coordinateInverse {N : ℕ} (i : Fin N)
    (f : TritWord N → ℤ) : coordinateZeta i (coordinateInverse i f) = f := by sorry
