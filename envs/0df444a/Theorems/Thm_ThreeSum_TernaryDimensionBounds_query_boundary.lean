-- Prove2me | Theorems.Thm_ThreeSum_TernaryDimensionBounds_query_boundary
-- name    : ThreeSum.TernaryDimensionBounds.query_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:26.878365+00:00
-- url     : https://prove2.me/theorems/74ac9a0c-27cc-4071-bf63-5440e9a6e998
-- title:
--   Ternary Dimension Bounds: query boundary
-- statement:
--   The Ternary Dimension Bounds construction uses the query boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L42-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L42-L47

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters

theorem ThreeSum.TernaryDimensionBounds.query_boundary {m j : ℕ} {Q : TritWord (fixedLength (j*m))}
    (hQ : HasType Q (fixedPi (j*m))) : rank Q+1-bankCut m j=queryDeficit m j := by sorry
