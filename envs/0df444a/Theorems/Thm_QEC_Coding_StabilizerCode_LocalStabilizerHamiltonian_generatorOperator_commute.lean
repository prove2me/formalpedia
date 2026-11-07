-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_generatorOperator_commute
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:49:58.060776+00:00
-- url     : https://prove2.me/theorems/70977ea0-6123-4029-b09d-fa5ebc7f7441
-- title:
--   Local Stabilizer Hamiltonian: generator Operator commute
-- statement:
--   Selected concrete generator operators commute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L145-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/LocalHamiltonian.lean#L145-L149

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.generatorOperator_commute
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ)) (j k : κ) :
    Commute (H.generatorOperator j) (H.generatorOperator k) := by sorry
