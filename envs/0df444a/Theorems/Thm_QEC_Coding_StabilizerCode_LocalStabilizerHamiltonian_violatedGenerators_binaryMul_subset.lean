-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_violatedGenerators_binaryMul_subset
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_binaryMul_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:28:14.761133+00:00
-- url     : https://prove2.me/theorems/ade42d38-b38e-4cda-8ce8-c044aa74a465
-- title:
--   Local Stabilizer Hamiltonian: violated Generators binary Mul subset
-- statement:
--   A selected syndrome can only be supported where one factor has syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L223-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/PathEnergy.lean#L223-L234

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.violatedGenerators_binaryMul_subset
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E F : Binary ι) :
    H.violatedGenerators (binaryMul E F) ⊆
      H.violatedGenerators E ∪ H.violatedGenerators F := by sorry
