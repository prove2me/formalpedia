-- Prove2me | Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
-- name    : ThreeSum.LightMomentDeterminant.eval_prodCircuits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:48.040036+00:00
-- url     : https://prove2.me/theorems/6e386a9f-18ab-4f68-9759-042550e99e8d
-- title:
--   Light Moment Determinant: eval prod Circuits
-- statement:
--   The Light Moment Determinant construction uses the eval prod Circuits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L19-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L19-L25

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators

theorem ThreeSum.LightMomentDeterminant.eval_prodCircuits (es : List Circuit) (x : ℕ → ℤ) :
    (prodCircuits es).eval x=(es.map (fun e => e.eval x)).prod := by sorry
