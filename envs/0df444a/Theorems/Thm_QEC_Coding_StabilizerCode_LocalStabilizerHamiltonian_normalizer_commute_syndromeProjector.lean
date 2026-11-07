-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_normalizer_commute_syndromeProjector
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.normalizer_commute_syndromeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:44.002787+00:00
-- url     : https://prove2.me/theorems/f99278d7-4897-494f-8d7f-e228fa772b90
-- title:
--   Local Stabilizer Hamiltonian: normalizer commute syndrome Projector
-- statement:
--   Every normalizer Pauli commutes with every joint syndrome projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L229-L236
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L229-L236

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.normalizer_commute_syndromeProjector
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    {logical : Binary ι} (hlogical : H.code.1.InBinaryNormalizer logical)
    (syndrome : DecoderSyndrome κ) :
    Commute (toHermitianQubitOperator logical) (H.syndromeProjector syndrome) := by sorry
