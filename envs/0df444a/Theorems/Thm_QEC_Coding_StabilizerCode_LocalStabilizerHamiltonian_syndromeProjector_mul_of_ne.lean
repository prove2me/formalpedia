-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_mul_of_ne
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:22.3172+00:00
-- url     : https://prove2.me/theorems/e050cc53-4619-46c8-a052-81a90570b707
-- title:
--   Local Stabilizer Hamiltonian: syndrome Projector mul of ne
-- statement:
--   Distinct syndrome sectors are orthogonal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L62-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L62-L67

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul_of_ne
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (left right : DecoderSyndrome κ) (hne : left ≠ right) :
    H.syndromeProjector left * H.syndromeProjector right = 0 := by sorry
