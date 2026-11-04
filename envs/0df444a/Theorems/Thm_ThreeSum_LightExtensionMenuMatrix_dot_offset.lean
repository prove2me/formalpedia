-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_dot_offset
-- name    : ThreeSum.LightExtensionMenuMatrix.dot_offset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:41.408725+00:00
-- url     : https://prove2.me/theorems/f8eb2d5f-9494-436d-bf19-88326ae11c97
-- title:
--   Light Extension Menu Matrix: dot offset
-- statement:
--   Reversing digit coordinates while keeping both tags fixed preserves a dot product.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuSemantics.lean#L40-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuSemantics.lean#L40-L56

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

theorem ThreeSum.LightExtensionMenuMatrix.dot_offset (J : ℕ) (f g : ℕ → ℕ) :
    LightNaturalDot.dot (fun i => f (TernarySignedLayout.offset J i))
      (fun i => g (TernarySignedLayout.offset J i)) (J+2)=LightNaturalDot.dot f g (J+2) := by sorry
