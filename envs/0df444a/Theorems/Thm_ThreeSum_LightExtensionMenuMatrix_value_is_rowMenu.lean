-- Prove2me | Theorems.Thm_ThreeSum_LightExtensionMenuMatrix_value_is_rowMenu
-- name    : ThreeSum.LightExtensionMenuMatrix.value_is_rowMenu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:04:05.144814+00:00
-- url     : https://prove2.me/theorems/6c60b53c-71b8-4759-89e8-c3db4718e4b0
-- title:
--   Light Extension Menu Matrix: value is row Menu
-- statement:
--   The Light Extension Menu Matrix construction uses the value is row Menu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuSemantics.lean#L19-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightExtensionMenuSemantics.lean#L19-L37

import Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuSemantics
import Theorems.Thm_ThreeSum_TernarySignedLayout_offset_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightExtensionMenuMatrix
open TernaryExtensionEncoding
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem ThreeSum.LightExtensionMenuMatrix.value_is_rowMenu (hf : f.Monic) (hd : 0 < f.natDegree)
    (J r : ℕ) (hr : r < (p^f.natDegree)*(p^f.natDegree)) {i : ℕ} (hi : i < J+2) :
    LightExtensionSeedMatrix.value (encodedMul hf) (p^f.natDegree) p r
      (TernarySignedLayout.offset J i)=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (seed hf r hr)
        ⟨TernarySignedLayout.offset J i,TernarySignedLayout.offset_lt hi⟩).val := by sorry
