-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_term_adjoint_eq_self
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:49:48.67306+00:00
-- url     : https://prove2.me/theorems/fd827ae3-4969-41b5-a04d-dd013971f7cf
-- title:
--   Local Stabilizer Hamiltonian: term adjoint eq self
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the term adjoint eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L139-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L139-L142

import Definitions.Def_QEC_Coding_Stabilizer_FixedGeneratorInteraction
import Definitions.Def_QEC_Locality_Core_Definitions
import Definitions.Def_QEC_Coding_Stabilizer_LocalHamiltonian
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open PauliSymplectic
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.term_adjoint_eq_self
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    LinearMap.adjoint (H.term j) = H.term j := by sorry
