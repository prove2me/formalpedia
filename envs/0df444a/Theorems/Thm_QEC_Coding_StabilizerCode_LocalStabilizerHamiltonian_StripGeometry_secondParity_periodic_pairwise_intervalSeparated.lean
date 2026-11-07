-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_secondParity_periodic_pairwise_intervalSeparated
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_periodic_pairwise_intervalSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:58.115455+00:00
-- url     : https://prove2.me/theorems/7c3453b7-06c2-436f-b0dd-469a08768aca
-- title:
--   Strip Geometry: second Parity periodic pairwise interval Separated
-- statement:
--   Periodic separation for the second parity, including the seam gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L568-L590
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L568-L590

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
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.secondParity_periodic_pairwise_intervalSeparated
    (L r : Nat) (widths : List Nat)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (secondParity (openStripListAux L 0 widths)).Pairwise
      (PeriodicIntervalSeparated L r) := by sorry
