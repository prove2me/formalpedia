-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openStripListAux_exists
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openStripListAux_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:31:46.069808+00:00
-- url     : https://prove2.me/theorems/8684fa4b-3ca3-4371-8372-2e375e48ad60
-- title:
--   Strip Geometry: mem open Strip List Aux exists
-- statement:
--   Every constructed strip remembers one of the supplied widths.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L327-L340
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L327-L340

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openStripListAux_exists
    {L start : Nat} {widths : List Nat}
    {R : Finset (Site L)} (hR : R ∈ openStripListAux L start widths) :
    ∃ stripStart width, width ∈ widths ∧
      R = openVerticalInterval L stripStart width := by sorry
