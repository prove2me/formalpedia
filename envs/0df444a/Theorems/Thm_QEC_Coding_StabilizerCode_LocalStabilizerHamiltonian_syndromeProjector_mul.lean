-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_mul
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:33:54.775412+00:00
-- url     : https://prove2.me/theorems/94f74dee-1c3d-4410-b697-cded11caecda
-- title:
--   Local Stabilizer Hamiltonian: syndrome Projector mul
-- statement:
--   Multiplication law for the orthogonal syndrome resolution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L76-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L76-L85

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_mul
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (left right : DecoderSyndrome κ) :
    H.syndromeProjector left * H.syndromeProjector right =
      if left = right then H.syndromeProjector left else 0 := by sorry
