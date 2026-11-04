-- Prove2me | Theorems.Thm_ThreeSum_TernaryDimensionBounds_output_rank
-- name    : ThreeSum.TernaryDimensionBounds.output_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:44.244975+00:00
-- url     : https://prove2.me/theorems/06ce0c03-6676-4ff9-ad20-19898f819e1d
-- title:
--   Ternary Dimension Bounds: output rank
-- statement:
--   The Ternary Dimension Bounds construction uses the output rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L36-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L36-L40

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters

theorem ThreeSum.TernaryDimensionBounds.output_rank {m j : ℕ} {Q : TritWord (fixedLength (j*m))}
    (hQ : HasType Q (fixedPi (j*m))) : rank Q = 21730058*j*m := by sorry
