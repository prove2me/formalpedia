-- Prove2me | Theorems.Thm_ThreeSum_TernaryExtensionEncoding_trajectory_rowMenu
-- name    : ThreeSum.TernaryExtensionEncoding.trajectory_rowMenu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:22.53607+00:00
-- url     : https://prove2.me/theorems/f7a77b0c-043c-4a14-b4a9-55676c1433c9
-- title:
--   Ternary Extension Encoding: trajectory row Menu
-- statement:
--   The Ternary Extension Encoding construction uses the trajectory row Menu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L99-L103
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryExtensionSeedSemantics.lean#L99-L103

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

theorem ThreeSum.TernaryExtensionEncoding.trajectory_rowMenu (hf : f.Monic) (hd : 0<f.natDegree) (Λ : ℕ)
    (x y : AdjoinRoot f) (i : Fin Λ) :
    (LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i.val)%p=
      (TernaryOriginalRowMenu.seedRow Λ (constantCoefficient hf hd) (x,y) i).val := by sorry
