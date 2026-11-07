-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openStripListAux_pairwise_periodicUnitSeparated
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_periodicUnitSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:25.801768+00:00
-- url     : https://prove2.me/theorems/51aa8bf9-5185-402b-8da4-583ebd458cf4
-- title:
--   Strip Geometry: open Strip List Aux pairwise periodic Unit Separated
-- statement:
--   Unit-gap strip lists are also separated from cyclic width-one intervals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L395-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L395-L409

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_periodicUnitSeparated
    (L : Nat) (widths : List Nat)
    (hPositive : ∀ width ∈ widths, 1 ≤ width) :
    (openStripListAux L 0 widths).Pairwise
      (PeriodicIntervalSeparated L 1) := by sorry
