-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openStripListAux_pairwise_openUnitSeparated
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_openUnitSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:13.466988+00:00
-- url     : https://prove2.me/theorems/36779e60-c719-44cd-9d14-f3d5e49c227e
-- title:
--   Strip Geometry: open Strip List Aux pairwise open Unit Separated
-- statement:
--   Unit-gap strip lists are separated from open intervals of width one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L386-L392
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L386-L392

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_openUnitSeparated
    (L start : Nat) (widths : List Nat)
    (hPositive : ∀ width ∈ widths, 1 ≤ width) :
    (openStripListAux L start widths).Pairwise
      (OpenIntervalSeparated L 1) := by sorry
