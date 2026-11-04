-- Prove2me | Theorems.Thm_ThreeSum_TernaryDimensionBounds_rank_eq_counts
-- name    : ThreeSum.TernaryDimensionBounds.rank_eq_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:16:28.232906+00:00
-- url     : https://prove2.me/theorems/2f31bd36-5e38-41d3-acb2-637a4b267a37
-- title:
--   Ternary Dimension Bounds: rank eq counts
-- statement:
--   The Ternary Dimension Bounds construction uses the rank eq counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L28-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryDimensionBounds.lean#L28-L34

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Definitions.Def_Submission_ThreeSum_TernaryDimensionBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryDimensionBounds
open TernaryJointType TernaryLocalParameters TernaryBank TernaryParameters

theorem ThreeSum.TernaryDimensionBounds.rank_eq_counts {N : ℕ} (Q : TritWord N) :
    rank Q = digitCount Q 1+2*digitCount Q 2 := by sorry
