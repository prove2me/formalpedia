-- Prove2me | Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_determinant
-- name    : ThreeSum.LightMomentDeterminant.eval_determinant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:35.832428+00:00
-- url     : https://prove2.me/theorems/266ae65e-66f8-4680-b096-a0ff6d4235b4
-- title:
--   Light Moment Determinant: eval determinant
-- statement:
--   The Light Moment Determinant construction uses the eval determinant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L32-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L32-L39

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators

theorem ThreeSum.LightMomentDeterminant.eval_determinant (d : ℕ) (entry : Fin d → Fin d → Circuit) (x : ℕ → ℤ) :
    (determinant d entry).eval x=Matrix.det (Matrix.of (fun i j => (entry i j).eval x)) := by sorry
