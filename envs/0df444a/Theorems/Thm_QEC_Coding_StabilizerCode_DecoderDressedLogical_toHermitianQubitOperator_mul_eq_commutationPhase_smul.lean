-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_DecoderDressedLogical_toHermitianQubitOperator_mul_eq_commutationPhase_smul
-- name    : QEC.Coding.StabilizerCode.DecoderDressedLogical.toHermitianQubitOperator_mul_eq_commutationPhase_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:17:18.53601+00:00
-- url     : https://prove2.me/theorems/d850c756-c070-4d44-b7f6-b54540bdef8c
-- title:
--   Decoder Dressed Logical: to Hermitian Qubit Operator mul eq commutation Phase smul
-- statement:
--   Concrete exchange law for Hermitian Pauli representatives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L84-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/GoodSyndromeProtectedSector.lean#L84-L97

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

theorem QEC.Coding.StabilizerCode.DecoderDressedLogical.toHermitianQubitOperator_mul_eq_commutationPhase_smul
    (left right : Binary ι) :
    toHermitianQubitOperator left * toHermitianQubitOperator right =
      commutationPhase left right •
        (toHermitianQubitOperator right * toHermitianQubitOperator left) := by sorry
