-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_XZAssembly_zCorrection_syndrome_eq
-- name    : QEC.Coding.MultiscaleDecoder.XZAssembly.zCorrection_syndrome_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:25:51.33099+00:00
-- url     : https://prove2.me/theorems/f6c41d18-4562-4766-bd16-32b08522f830
-- title:
--   XZAssembly: z Correction syndrome eq
-- statement:
--   The XZAssembly construction uses the z Correction syndrome eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1511-L1516
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1511-L1516

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
open QEC.Coding.MultiscaleDecoder.XZAssembly
variable {DX : BDL26DecoderData depth C0 C1 C2}
variable {Z0 Z1 Z2 : LevelIndex depth → Type v}
variable [∀ i, Fintype (Z0 i)] [∀ i, Fintype (Z1 i)] [∀ i, Fintype (Z2 i)]

theorem QEC.Coding.MultiscaleDecoder.XZAssembly.zCorrection_syndrome_eq
    (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : A.DZ.family.Syndrome (TopIndex depth)) :
    A.DZ.family.coboundary1 (TopIndex depth) (A.zCorrection sigma) =
      (sigma : A.DZ.family.Cochain2 (TopIndex depth)) := by sorry
