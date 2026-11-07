-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_syndromeProjector_adjoint
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:13:00.970936+00:00
-- url     : https://prove2.me/theorems/c5cb4851-20e0-42eb-98e9-228853ad7507
-- title:
--   Local Stabilizer Hamiltonian: syndrome Projector adjoint
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the syndrome Projector adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L46-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/DecoderDressedLogical.lean#L46-L51

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.syndromeProjector_adjoint
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (syndrome : DecoderSyndrome κ) :
    LinearMap.adjoint (H.syndromeProjector syndrome) =
      H.syndromeProjector syndrome := by sorry
