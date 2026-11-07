-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_logicalCoset_binaryMul_generated_iff_for_strip_cleaning
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.logicalCoset_binaryMul_generated_iff_for_strip_cleaning
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:37.172815+00:00
-- url     : https://prove2.me/theorems/ae836586-6dbc-4e31-8153-ce350da4b057
-- title:
--   Local Stabilizer Hamiltonian: logical Coset binary Mul generated iff for strip cleaning
-- statement:
--   Multiplication by an actual generated stabilizer preserves the nontrivial
--   logical coset.  This is kept in the strip module so that the BT09 distance
--   route depends only on the cleaning API, rather than on the later path-energy
--   module.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1196-L1220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1196-L1220

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.logicalCoset_binaryMul_generated_iff_for_strip_cleaning
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (E S : Binary ι) (hS : S ∈ H.code.1.generatedGroup) :
    (H.code.1.InBinaryNormalizer (binaryMul E S) ∧
        ¬ H.code.1.InGeneratedGroupUpToSign (binaryMul E S)) ↔
      (H.code.1.InBinaryNormalizer E ∧
        ¬ H.code.1.InGeneratedGroupUpToSign E) := by sorry
