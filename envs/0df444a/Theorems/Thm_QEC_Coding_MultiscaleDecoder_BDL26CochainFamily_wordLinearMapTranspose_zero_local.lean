-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_BDL26CochainFamily_wordLinearMapTranspose_zero_local
-- name    : QEC.Coding.MultiscaleDecoder.BDL26CochainFamily.wordLinearMapTranspose_zero_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:06:59.009089+00:00
-- url     : https://prove2.me/theorems/02b4be01-7405-4143-a130-e9a7d12da61e
-- title:
--   BDL26 Cochain Family: word Linear Map Transpose zero local
-- statement:
--   The BDL26 Cochain Family construction uses the word Linear Map Transpose zero local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L126-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Multiscale.lean#L126-L134

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

theorem QEC.Coding.MultiscaleDecoder.BDL26CochainFamily.wordLinearMapTranspose_zero_local
    {F : Type u} [Field F] [Fintype F]
    {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ] :
    wordLinearMapTranspose (0 : Word F ι →ₗ[F] Word F κ) = 0 := by sorry
