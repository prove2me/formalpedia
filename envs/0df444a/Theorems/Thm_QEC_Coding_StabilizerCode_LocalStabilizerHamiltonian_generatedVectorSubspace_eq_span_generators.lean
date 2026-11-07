-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatedVectorSubspace_eq_span_generators
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatedVectorSubspace_eq_span_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:26:14.735185+00:00
-- url     : https://prove2.me/theorems/0b966ae6-e087-4b01-b747-999c76200703
-- title:
--   Local Stabilizer Hamiltonian: generated Vector Subspace eq span generators
-- statement:
--   The existing generated stabilizer subspace is spanned by the selected family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Cleaning.lean#L67-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Cleaning.lean#L67-L87

import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_generatedVectorSubspace_eq_span_generators

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatedVectorSubspace_eq_span_generators
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) :
    H.code.1.generatedVectorSubspace =
      Submodule.span (ZMod 2)
        (Set.range fun j => (H.generators j).vector) := by sorry
