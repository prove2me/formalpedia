-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pauli_mul_syndromeProjector
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pauli_mul_syndromeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:14:23.061466+00:00
-- url     : https://prove2.me/theorems/8cbc031c-a284-4c2f-aeb2-f0ceabb3c3fd
-- title:
--   Local Stabilizer Hamiltonian: pauli mul syndrome Projector
-- statement:
--   A Pauli error transports the full joint syndrome projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L209-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L209-L216

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
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
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pauli_mul_syndromeProjector
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (error : Binary ι) (syndrome : DecoderSyndrome κ) :
    toHermitianQubitOperator error * H.syndromeProjector syndrome =
      H.syndromeProjector (H.transportSyndrome error syndrome) *
        toHermitianQubitOperator error := by sorry
