-- Prove2me | Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
-- name    : ThreeSum.LightMomentDeterminant.eval_sumCircuits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:39:35.646255+00:00
-- url     : https://prove2.me/theorems/93d5cfca-dad6-49b7-806c-39ea5735a012
-- title:
--   Light Moment Determinant: eval sum Circuits
-- statement:
--   The Light Moment Determinant construction uses the eval sum Circuits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L11-L17
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentDeterminant.lean#L11-L17

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators

theorem ThreeSum.LightMomentDeterminant.eval_sumCircuits (es : List Circuit) (x : ℕ → ℤ) :
    (sumCircuits es).eval x=(es.map (fun e => e.eval x)).sum := by sorry
