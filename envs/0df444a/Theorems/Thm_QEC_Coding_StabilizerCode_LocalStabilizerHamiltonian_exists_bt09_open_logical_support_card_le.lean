-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_bt09_open_logical_support_card_le
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_bt09_open_logical_support_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:45.929396+00:00
-- url     : https://prove2.me/theorems/11a1fe71-8118-4041-80d7-325bfa4deb25
-- title:
--   Local Stabilizer Hamiltonian: exists bt09 open logical support card le
-- statement:
--   Explicit open-boundary linear-support form of the BT09 proposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1460-L1483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1460-L1483

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_bt09_open_logical_support_card_le
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ r * L := by sorry
