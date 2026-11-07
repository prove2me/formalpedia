-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_inBinaryNormalizer_of_commutes_selectedGenerators
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inBinaryNormalizer_of_commutes_selectedGenerators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:36:57.803198+00:00
-- url     : https://prove2.me/theorems/db19b347-ada6-4e3b-91d4-b41ef1206fae
-- title:
--   Local Stabilizer Hamiltonian: in Binary Normalizer of commutes selected Generators
-- statement:
--   Commuting with every selected generator implies membership in the existing normalizer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L824-L835
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L824-L835

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.inBinaryNormalizer_of_commutes_selectedGenerators
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E : Binary ι) (hcommutes : ∀ j, Commutes E (H.generators j)) :
    H.code.1.InBinaryNormalizer E := by sorry
