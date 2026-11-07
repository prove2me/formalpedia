-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_bt09_periodic_unit_range_logical_support_card_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_bt09_periodic_unit_range_logical_support_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:38:14.745406+00:00
-- url     : https://prove2.me/theorems/89ee9764-1ba7-418f-9a85-7f0374489c93
-- title:
--   Local Stabilizer Hamiltonian: exists bt09 periodic unit range logical support card le
-- statement:
--   The explicit degenerate `r = 1` periodic-boundary branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1566-L1617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1566-L1617

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_bt09_periodic_unit_range_logical_support_card_le
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hLocal : StripGeometry.HasPeriodicIntervalGeneratorSupport H 1)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ L := by sorry
