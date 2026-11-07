-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openStripListAux_pairwise_disjoint
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:31:59.728798+00:00
-- url     : https://prove2.me/theorems/95c6ae40-169d-471d-837a-5c4047b775c5
-- title:
--   Strip Geometry: open Strip List Aux pairwise disjoint
-- statement:
--   Consecutive strips are pairwise disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L343-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L343-L360

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_disjoint
    (L start : Nat) (widths : List Nat) :
    (openStripListAux L start widths).Pairwise Disjoint := by sorry
