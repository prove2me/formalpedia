-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_signed_lift_cast
-- name    : ThreeSum.TernaryExtensionEncoding.signed_lift_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:21.332789+00:00
-- url     : https://prove2.me/theorems/2bea3c1a-d98e-459f-a65d-87abbe9267a4
-- title:
--   Ternary Extension Encoding: signed lift cast
-- statement:
--   The Ternary Extension Encoding construction uses the signed lift cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L106-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L106-L110

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
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem ThreeSum.TernaryExtensionEncoding.signed_lift_cast (z : ℤ) (hz : 0≤z+(p : ℤ)) :
    (((z+(p : ℤ)).toNat : ℕ) : ZMod p)=(z : ZMod p) := by sorry
