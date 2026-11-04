-- Prove2me | Theorems.Thm_ThreeSum_TernaryDimensionBounds_query_log_bound
-- name    : ThreeSum.TernaryDimensionBounds.query_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:44.75186+00:00
-- url     : https://prove2.me/theorems/566e0727-ac84-4845-aef0-1be1ad85dd48
-- title:
--   Ternary Dimension Bounds: query log bound
-- statement:
--   The Ternary Dimension Bounds construction uses the query log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L76-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L76-L99

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters

theorem ThreeSum.TernaryDimensionBounds.query_log_bound {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    Real.log ((nearWords Q (queryDeficit m j)).card : ℝ) ≤
      (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-Real.log z := by sorry
