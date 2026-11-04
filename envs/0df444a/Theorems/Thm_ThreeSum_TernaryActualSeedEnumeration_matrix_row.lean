-- Prove2me | Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_matrix_row
-- name    : ThreeSum.TernaryActualSeedEnumeration.matrix_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:16.48703+00:00
-- url     : https://prove2.me/theorems/017d81ca-187c-4996-9b35-9e9ba14ee306
-- title:
--   Ternary Actual Seed Enumeration: matrix row
-- statement:
--   The actual integer menu ordinal realizes the original extension-field
--   row, including its physical reversal of only the digit coordinates.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L29-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L29-L37

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryActualSeedEnumeration
open TernaryExtensionEncoding Polynomial
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryActualSeedEnumeration.matrix_row (hf : f.Monic) (hd : 0<f.natDegree) (J : ℕ)
    (x y : AdjoinRoot f) (i : Fin (J+2)) :
    LightExtensionSeedMatrix.value (encodedMul hf) (p^f.natDegree) p
      (equiv hf (x,y)).val (TernarySignedLayout.offset J i.val)=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y)
        (digitOrder J i)).val := by sorry
