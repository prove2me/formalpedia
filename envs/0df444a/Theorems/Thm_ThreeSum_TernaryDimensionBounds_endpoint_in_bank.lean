-- Prove2me | Theorems.Thm_ThreeSum_TernaryDimensionBounds_endpoint_in_bank
-- name    : ThreeSum.TernaryDimensionBounds.endpoint_in_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:24.117709+00:00
-- url     : https://prove2.me/theorems/34d898b7-2919-4c38-9635-0ca7cb712fd1
-- title:
--   Ternary Dimension Bounds: endpoint in bank
-- statement:
--   The Ternary Dimension Bounds construction uses the endpoint in bank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L49-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L49-L55

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters

theorem ThreeSum.TernaryDimensionBounds.endpoint_in_bank {m j : ℕ} {A : TritWord (fixedLength (j*m))}
    (hA : HasType A (fixedAlpha (j*m))) : A ∈ bank (fixedLength (j*m)) (bankCut m j) := by sorry
