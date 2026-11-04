-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_trajectory_encode
-- name    : ThreeSum.TernaryExtensionEncoding.trajectory_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:54.661197+00:00
-- url     : https://prove2.me/theorems/45d1382f-4ced-41ff-a2b3-9df05e30e040
-- title:
--   Ternary Extension Encoding: trajectory encode
-- statement:
--   The Ternary Extension Encoding construction uses the trajectory encode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L35-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L35-L41

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedRow
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] ThreeSum.TernaryExtensionEncoding._p2m_local_instance_7138b7e7ca_12
variable {f : (ZMod p)[X]}

theorem ThreeSum.TernaryExtensionEncoding.trajectory_encode (hf : f.Monic) (x y : AdjoinRoot f) (i : ℕ) :
    LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i=
      encode hf (y*x^i) := by sorry
