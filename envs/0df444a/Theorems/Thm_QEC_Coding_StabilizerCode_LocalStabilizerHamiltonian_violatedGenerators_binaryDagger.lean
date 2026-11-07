-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryDagger
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_binaryDagger
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:27:35.070403+00:00
-- url     : https://prove2.me/theorems/3c2bde58-e310-4248-b03b-aec77b9f511b
-- title:
--   Local Stabilizer Hamiltonian: violated Generators binary Dagger
-- statement:
--   Dagger does not change the selected violated-generator set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L261-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L261-L267

import Definitions.Def_QEC_Coding_Stabilizer_Energy
import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Coding_Stabilizer_PathEnergy
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open PauliSymplectic
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
open QEC.Coding.StabilizerCode QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_binaryDagger
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) :
    H.violatedGenerators (binaryDagger E) = H.violatedGenerators E := by sorry
