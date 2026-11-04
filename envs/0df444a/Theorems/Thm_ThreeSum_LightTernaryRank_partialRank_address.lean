-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_address
-- name    : ThreeSum.LightTernaryRank.partialRank_address
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:42:37.143341+00:00
-- url     : https://prove2.me/theorems/5abefec8-aa29-43b5-892a-62788fbc10dc
-- title:
--   Light Ternary Rank: partial Rank address
-- statement:
--   The Light Ternary Rank construction uses the partial Rank address property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L27-L32
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRank.lean#L27-L32

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryRank
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRank
open Light Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.LightSubsetAddress

theorem ThreeSum.LightTernaryRank.partialRank_address {N : ℕ} (w : TritWord N) : partialRank N (address w) N=rank w := by sorry
