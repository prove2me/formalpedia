-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_pauli_mul_syndromeProjectorOn
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pauli_mul_syndromeProjectorOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:16:53.833397+00:00
-- url     : https://prove2.me/theorems/b411bb0c-ea12-4a31-a1a9-40ec529f6fa8
-- title:
--   Local Stabilizer Hamiltonian: pauli mul syndrome Projector On
-- statement:
--   Pauli transport through any restricted product of syndrome factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L150-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L150-L206

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.pauli_mul_syndromeProjectorOn
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (error : Binary ι) (syndrome : DecoderSyndrome κ)
    (selected : Finset κ) :
    toHermitianQubitOperator error *
        selected.noncommProd (jointStabilizerFactor H.generators syndrome)
          (H.syndromeFactor_pairwise syndrome selected) =
      selected.noncommProd
          (jointStabilizerFactor H.generators
            (H.transportSyndrome error syndrome))
          (H.syndromeFactor_pairwise
            (H.transportSyndrome error syndrome) selected) *
        toHermitianQubitOperator error := by sorry
