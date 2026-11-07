-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_sum_syndromeProjector_eq_one
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.sum_syndromeProjector_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:46.79359+00:00
-- url     : https://prove2.me/theorems/6ef520cd-3143-4504-8fb4-772d4cdcf8cb
-- title:
--   Local Stabilizer Hamiltonian: sum syndrome Projector eq one
-- statement:
--   The full finite syndrome resolution sums to the identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L70-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L70-L73

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.sum_syndromeProjector_eq_one
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    ∑ syndrome : DecoderSyndrome κ, H.syndromeProjector syndrome = 1 := by sorry
