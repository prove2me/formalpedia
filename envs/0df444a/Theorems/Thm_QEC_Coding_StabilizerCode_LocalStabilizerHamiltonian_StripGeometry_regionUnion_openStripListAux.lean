-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_regionUnion_openStripListAux
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.regionUnion_openStripListAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:33:23.937291+00:00
-- url     : https://prove2.me/theorems/225938d8-15df-4e8b-a529-f90e4127f7e6
-- title:
--   Strip Geometry: region Union open Strip List Aux
-- statement:
--   Consecutive strips combine to the single interval of their total width.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L696-L715
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L696-L715

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.regionUnion_openStripListAux
    (L start : Nat) (widths : List Nat) :
    regionUnion (openStripListAux L start widths) =
      openVerticalInterval L start widths.sum := by sorry
