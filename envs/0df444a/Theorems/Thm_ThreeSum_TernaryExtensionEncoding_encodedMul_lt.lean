-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_encodedMul_lt
-- name    : ThreeSum.TernaryExtensionEncoding.encodedMul_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:23.083092+00:00
-- url     : https://prove2.me/theorems/e822e8e2-dace-461d-a001-65120b92eb4e
-- title:
--   Ternary Extension Encoding: encoded Mul lt
-- statement:
--   The Ternary Extension Encoding construction uses the encoded Mul lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L20-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L20-L25

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

theorem ThreeSum.TernaryExtensionEncoding.encodedMul_lt (hf : f.Monic) (a b : ℕ) : encodedMul hf a b<p^f.natDegree := by sorry
