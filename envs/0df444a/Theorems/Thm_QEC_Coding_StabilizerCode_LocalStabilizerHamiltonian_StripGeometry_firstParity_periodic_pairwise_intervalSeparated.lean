-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_firstParity_periodic_pairwise_intervalSeparated
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_periodic_pairwise_intervalSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:36:30.385604+00:00
-- url     : https://prove2.me/theorems/2efcfaae-0df1-4ee4-8ec6-772bc23fd15e
-- title:
--   Strip Geometry: first Parity periodic pairwise interval Separated
-- statement:
--   Periodic separation for the first parity, including the seam gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L545-L565
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L545-L565

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.firstParity_periodic_pairwise_intervalSeparated
    (L r : Nat) (widths : List Nat)
    (hSum : widths.sum = L)
    (hEven : Even widths.length)
    (hLower : ∀ width ∈ widths, r - 1 ≤ width) :
    (firstParity (openStripListAux L 0 widths)).Pairwise
      (PeriodicIntervalSeparated L r) := by sorry
