-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_commutationPhase_binaryMul_left
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.commutationPhase_binaryMul_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:16:59.984388+00:00
-- url     : https://prove2.me/theorems/6308e27e-f861-4178-ac25-984eaaba991f
-- title:
--   Decoder Dressed Logical: commutation Phase binary Mul left
-- statement:
--   The commutation sign is multiplicative in a Pauli product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L53-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L53-L66

import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_Stabilizer_GoodSyndromeProtectedSector
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]
open QEC.Coding.StabilizerCode.DecoderDressedLogical
variable {H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)}

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.commutationPhase_binaryMul_left
    (left middle right : Binary ι) :
    commutationPhase (binaryMul left middle) right =
      commutationPhase left right * commutationPhase middle right := by sorry
