-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_DualSectorAssembly_xCorrection_syndrome_eq
-- name    : QEC.Coding.MultiscaleDecoder.DualSectorAssembly.xCorrection_syndrome_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:28:46.044873+00:00
-- url     : https://prove2.me/theorems/7260a780-1c28-4b08-a3dc-10dea3aa532f
-- title:
--   Dual Sector Assembly: x Correction syndrome eq
-- statement:
--   The Dual Sector Assembly construction uses the x Correction syndrome eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1555-L1561
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1555-L1561

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
open QEC.Coding.MultiscaleDecoder.DualSectorAssembly
variable {DX : BDL26DecoderData depth C0 C1 C2}

theorem QEC.Coding.MultiscaleDecoder.DualSectorAssembly.xCorrection_syndrome_eq
    (A : DualSectorAssembly DX)
    (sigma : DX.family.Syndrome (TopIndex depth)) :
    DX.family.coboundary1 (TopIndex depth)
        ((A.toXZAssembly).xCorrection sigma) =
      (sigma : DX.family.Cochain2 (TopIndex depth)) := by sorry
