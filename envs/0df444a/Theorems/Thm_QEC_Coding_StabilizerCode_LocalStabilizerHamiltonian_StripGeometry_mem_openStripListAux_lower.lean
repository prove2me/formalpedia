-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_mem_openStripListAux_lower
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openStripListAux_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:31:58.671456+00:00
-- url     : https://prove2.me/theorems/b86bac8f-8551-4376-8516-91d65f162c43
-- title:
--   Strip Geometry: mem open Strip List Aux lower
-- statement:
--   Every site in a generated strip lies weakly to the right of its start.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L312-L324
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L312-L324

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.mem_openStripListAux_lower
    {L start : Nat} {widths : List Nat}
    {R : Finset (Site L)} (hR : R ∈ openStripListAux L start widths)
    {p : Site L} (hp : p ∈ R) :
    start ≤ p.1.val := by sorry
