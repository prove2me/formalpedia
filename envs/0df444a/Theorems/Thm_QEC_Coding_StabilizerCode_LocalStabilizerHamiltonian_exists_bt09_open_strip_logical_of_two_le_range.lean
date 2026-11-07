-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_bt09_open_strip_logical_of_two_le_range
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_bt09_open_strip_logical_of_two_le_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:38:00.469195+00:00
-- url     : https://prove2.me/theorems/e14bb41e-76d7-4a11-9f45-f1627a7e6dc5
-- title:
--   Local Stabilizer Hamiltonian: exists bt09 open strip logical of two le range
-- statement:
--   The nondegenerate open-boundary BT09 conclusion: at the exact source
--   threshold, some nontrivial logical representative is supported in a concrete
--   vertical strip whose width is `r - 1` or `r`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1320-L1385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1320-L1385

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_bt09_open_strip_logical_of_two_le_range
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ start width, (width = r - 1 ∨ width = r) ∧
      ∃ Q : Binary (StripGeometry.Site L),
        H.code.1.InBinaryNormalizer Q ∧
        ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
        support Q ⊆
          StripGeometry.openVerticalInterval L start width := by sorry
