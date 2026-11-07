-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_bt09_open_linear_distance
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.bt09_open_linear_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:01:15.833468+00:00
-- url     : https://prove2.me/theorems/92e5694b-75fa-461d-b99d-8fb35ed7974c
-- title:
--   Local Stabilizer Hamiltonian: bt09 open linear distance
-- statement:
--   BT09's open-boundary linear-distance proposition, including the explicit
--   `r = 1` branch and the exact `L ≥ 2(r-1)^2` threshold.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1623-L1644
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L1623-L1644

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.bt09_open_linear_distance
    {L r : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (hr : 1 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L)
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (P : Binary (StripGeometry.Site L))
    (hPNormalizer : H.code.1.InBinaryNormalizer P)
    (hPNontrivial : ¬ H.code.1.InGeneratedGroupUpToSign P) :
    ∃ Q : Binary (StripGeometry.Site L),
      H.code.1.InBinaryNormalizer Q ∧
      ¬ H.code.1.InGeneratedGroupUpToSign Q ∧
      (support Q).card ≤ r * L := by sorry
