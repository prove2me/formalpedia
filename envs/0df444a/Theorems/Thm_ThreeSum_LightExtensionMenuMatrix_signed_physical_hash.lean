-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_signed_physical_hash
-- name    : ThreeSum.LightExtensionMenuMatrix.signed_physical_hash
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:22.503108+00:00
-- url     : https://prove2.me/theorems/d97dd22d-71ad-4ce4-99ba-23e36eb82a2e
-- title:
--   Light Extension Menu Matrix: signed physical hash
-- statement:
--   The exact integer hash returned by SignedRowHash is the original logical row functional.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuSemantics.lean#L60-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuSemantics.lean#L60-L87

import Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMenuMatrix
open TernaryExtensionEncoding
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem ThreeSum.LightExtensionMenuMatrix.signed_physical_hash (hf : f.Monic) (hd : 0 < f.natDegree)
    (J : ℕ) (x y : AdjoinRoot f) (raw : ℕ → ℤ)
    (hlift : ∀ i < J+2, 0 ≤ (p : ℤ)+raw i) :
    LightNaturalDot.dot
      (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y)
        (TernarySignedLayout.offset J i)%p)
      (fun i => ((p : ℤ)+raw (TernarySignedLayout.offset J i)).toNat) (J+2)%p=
      (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
        (fun i => (raw i.val : ZMod p))).val := by sorry
