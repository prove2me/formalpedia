-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorSupport_eq_support
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:51:41.237562+00:00
-- url     : https://prove2.me/theorems/1e6acf49-f755-474a-9b25-25e5123db0fe
-- title:
--   Local Stabilizer Hamiltonian: generator Support eq support
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the generator Support eq support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L63-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L63-L66

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    H.generatorSupport j = support (H.generators j) := by sorry

attribute [defeq] QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorSupport_eq_support
