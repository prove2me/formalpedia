-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_coboundary1_comp_coboundary0
-- name    : QEC.Coding.MultiscaleDecoder.BDL26CochainFamily.coboundary1_comp_coboundary0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:21:02.292219+00:00
-- url     : https://prove2.me/theorems/fffaea7b-261b-4b32-8bcc-57cb75aef324
-- title:
--   BDL26 Cochain Family: coboundary1 comp coboundary0
-- statement:
--   The BDL26 Cochain Family construction uses the coboundary1 comp coboundary0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L136-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L136-L151

import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_Graph_Core
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z a
variable {depth : Nat}
open QEC.Coding.MultiscaleDecoder.BDL26CochainFamily
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.BDL26CochainFamily.coboundary1_comp_coboundary0
    (F : BDL26CochainFamily depth C0 C1 C2)
    (i : LevelIndex depth) :
    (F.coboundary1 i).comp (F.coboundary0 i) =
      (0 : F.Cochain0 i →ₗ[BDL26Field] F.Cochain2 i) := by sorry
