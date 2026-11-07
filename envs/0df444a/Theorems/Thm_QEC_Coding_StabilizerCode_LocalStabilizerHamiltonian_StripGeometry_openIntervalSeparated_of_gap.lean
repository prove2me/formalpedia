-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_StripGeometry_openIntervalSeparated_of_gap
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openIntervalSeparated_of_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:32:52.470193+00:00
-- url     : https://prove2.me/theorems/f5eefbd2-f445-4b95-bb79-31693c059106
-- title:
--   Strip Geometry: open Interval Separated of gap
-- statement:
--   The Strip Geometry construction uses the open Interval Separated of gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L188-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L188-L206

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.StripGeometry.openIntervalSeparated_of_gap
    {L r : Nat} {A B : Finset (Site L)}
    (hgap : OpenSeparatedByGap r A B) :
    OpenIntervalSeparated L r A B := by sorry
