-- Prove2me | Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_leading
-- name    : ThreeSum.LightMomentDeterminant.eval_leading
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:30.722495+00:00
-- url     : https://prove2.me/theorems/2088b12f-962d-46c6-991f-75f28903502c
-- title:
--   Light Moment Determinant: eval leading
-- statement:
--   The Light Moment Determinant construction uses the eval leading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L50-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L50-L53

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators

theorem ThreeSum.LightMomentDeterminant.eval_leading (d : ℕ) (x : ℕ → ℤ) :
    (leading d).eval x=Matrix.det (Matrix.of (fun (i j : Fin d) => x (i.val+j.val+1))) := by sorry
