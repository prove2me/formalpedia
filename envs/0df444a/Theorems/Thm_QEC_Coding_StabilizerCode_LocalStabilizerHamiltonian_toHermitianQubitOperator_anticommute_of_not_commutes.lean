-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_toHermitianQubitOperator_anticommute_of_not_commutes
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.toHermitianQubitOperator_anticommute_of_not_commutes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:51.503064+00:00
-- url     : https://prove2.me/theorems/ba7d103f-7708-4666-9b27-e4134c4bceab
-- title:
--   Local Stabilizer Hamiltonian: to Hermitian Qubit Operator anticommute of not commutes
-- statement:
--   A signed Hermitian Pauli anticommutes concretely when its binary words do.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L103-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L103-L110

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.toHermitianQubitOperator_anticommute_of_not_commutes
    (P Q : Binary ι) (h : ¬ Commutes P Q) :
    toHermitianQubitOperator P * toHermitianQubitOperator Q =
      -(toHermitianQubitOperator Q * toHermitianQubitOperator P) := by sorry
