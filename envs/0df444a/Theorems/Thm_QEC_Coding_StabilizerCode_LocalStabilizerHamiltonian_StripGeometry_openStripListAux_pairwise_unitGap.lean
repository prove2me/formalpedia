-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openStripListAux_pairwise_unitGap
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_unitGap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:34.34371+00:00
-- url     : https://prove2.me/theorems/36ce3125-6373-46ce-b20c-c66c83a0b247
-- title:
--   Strip Geometry: open Strip List Aux pairwise unit Gap
-- statement:
--   Distinct consecutive positive-width strips have at least the unit gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L363-L383
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L363-L383

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openStripListAux_pairwise_unitGap
    (L start : Nat) (widths : List Nat)
    (hPositive : ∀ width ∈ widths, 1 ≤ width) :
    (openStripListAux L start widths).Pairwise
      (OpenSeparatedByGap 1) := by sorry
