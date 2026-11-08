-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_DualSectorAssembly_family_complex_eq_dual
-- name    : QEC.Coding.MultiscaleDecoder.DualSectorAssembly.family_complex_eq_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:30:00.94188+00:00
-- url     : https://prove2.me/theorems/d9f1b8dd-9673-44d1-a23c-67d72c8fee7b
-- title:
--   Dual Sector Assembly: family complex eq dual
-- statement:
--   The Dual Sector Assembly construction uses the family complex eq dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1549-L1553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1549-L1553

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

theorem QEC.Coding.MultiscaleDecoder.DualSectorAssembly.family_complex_eq_dual
    (A : DualSectorAssembly DX) (i : LevelIndex depth) :
    A.DZ.family.complex i = dualChainComplex (DX.family.complex i) := by sorry
