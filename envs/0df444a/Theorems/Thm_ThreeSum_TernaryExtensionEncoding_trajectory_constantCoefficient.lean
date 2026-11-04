-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_trajectory_constantCoefficient
-- name    : ThreeSum.TernaryExtensionEncoding.trajectory_constantCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:16.234027+00:00
-- url     : https://prove2.me/theorems/d99eac93-abc5-4e3d-b1dc-2aacf6eaab8b
-- title:
--   Ternary Extension Encoding: trajectory constant Coefficient
-- statement:
--   The Ternary Extension Encoding construction uses the trajectory constant Coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L43-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L43-L47

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

theorem ThreeSum.TernaryExtensionEncoding.trajectory_constantCoefficient (hf : f.Monic) (hd : 0<f.natDegree)
    (x y : AdjoinRoot f) (i : ℕ) :
    (LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i)%p=
      (constantCoefficient hf hd (y*x^i)).val := by sorry
