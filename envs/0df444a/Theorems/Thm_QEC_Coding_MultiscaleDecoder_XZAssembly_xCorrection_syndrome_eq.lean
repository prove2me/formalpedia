-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_XZAssembly_xCorrection_syndrome_eq
-- name    : QEC.Coding.MultiscaleDecoder.XZAssembly.xCorrection_syndrome_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:24:52.095212+00:00
-- url     : https://prove2.me/theorems/3f5f2f4b-cdb2-4472-ba85-2fa324997dee
-- title:
--   XZAssembly: x Correction syndrome eq
-- statement:
--   The XZAssembly construction uses the x Correction syndrome eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1504-L1509
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1504-L1509

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

theorem QEC.Coding.MultiscaleDecoder.XZAssembly.xCorrection_syndrome_eq
    (A : XZAssembly (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) DX)
    (sigma : DX.family.Syndrome (TopIndex depth)) :
    DX.family.coboundary1 (TopIndex depth) (A.xCorrection sigma) =
      (sigma : DX.family.Cochain2 (TopIndex depth)) := by sorry
