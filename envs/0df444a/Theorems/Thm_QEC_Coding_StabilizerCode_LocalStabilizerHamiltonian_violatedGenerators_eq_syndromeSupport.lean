-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_eq_syndromeSupport
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_eq_syndromeSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:24:36.379792+00:00
-- url     : https://prove2.me/theorems/adba78cc-20df-4c6b-9709-b0ae499065bf
-- title:
--   Local Stabilizer Hamiltonian: violated Generators eq syndrome Support
-- statement:
--   Violated selected terms are exactly the nonzero selected syndrome bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L88-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Energy.lean#L88-L93

import Definitions.Def_QEC_Coding_Stabilizer_ErrorPath
import Definitions.Def_QEC_Coding_Stabilizer_Energy
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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_eq_syndromeSupport
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.violatedGenerators E = H.syndromeSupport E := by sorry
