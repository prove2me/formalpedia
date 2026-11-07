-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pauli_mul_jointStabilizerFactor
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pauli_mul_jointStabilizerFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:15:38.034577+00:00
-- url     : https://prove2.me/theorems/1df737e3-4e23-40e2-93c4-8340697be6d8
-- title:
--   Local Stabilizer Hamiltonian: pauli mul joint Stabilizer Factor
-- statement:
--   One Pauli transports one selected spectral factor to the flipped sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L113-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L113-L137

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pauli_mul_jointStabilizerFactor
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (error : Binary ι) (syndrome : DecoderSyndrome κ) (check : κ) :
    toHermitianQubitOperator error *
        jointStabilizerFactor H.generators syndrome check =
      jointStabilizerFactor H.generators
          (H.transportSyndrome error syndrome) check *
        toHermitianQubitOperator error := by sorry
