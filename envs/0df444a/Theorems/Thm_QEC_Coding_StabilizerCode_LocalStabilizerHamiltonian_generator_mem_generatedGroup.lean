-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generator_mem_generatedGroup
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generator_mem_generatedGroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:50:20.641939+00:00
-- url     : https://prove2.me/theorems/08dd06b2-2680-406c-9da3-747c0d79b696
-- title:
--   Local Stabilizer Hamiltonian: generator mem generated Group
-- statement:
--   One selected generator belongs to the existing code's generated group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L69-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L69-L73

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generator_mem_generatedGroup
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j : κ) :
    H.generators j ∈ H.code.1.generatedGroup := by sorry
