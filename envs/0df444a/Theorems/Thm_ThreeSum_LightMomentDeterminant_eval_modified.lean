-- Prove2me | Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_modified
-- name    : ThreeSum.LightMomentDeterminant.eval_modified
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:07.372188+00:00
-- url     : https://prove2.me/theorems/ae150eb5-0905-40ba-ab02-2a5eedd7a352
-- title:
--   Light Moment Determinant: eval modified
-- statement:
--   The Light Moment Determinant construction uses the eval modified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L55-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L55-L61

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators

theorem ThreeSum.LightMomentDeterminant.eval_modified (d : ℕ) (x : ℕ → ℤ) :
    (modified d).eval x=Matrix.det (Matrix.of (fun (i j : Fin d) =>
      x (i.val+j.val+3)-2*x 0*x (i.val+j.val+2)+(x 0)^2*x (i.val+j.val+1))) := by sorry
