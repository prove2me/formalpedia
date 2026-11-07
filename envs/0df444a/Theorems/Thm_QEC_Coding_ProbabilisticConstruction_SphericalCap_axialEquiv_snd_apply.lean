-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:48:56.66319+00:00
-- url     : https://prove2.me/theorems/060bb8f3-d037-4133-bad4-b70a8c7264a5
-- title:
--   Spherical Cap: axial Equiv snd apply
-- statement:
--   The Spherical Cap construction uses the axial Equiv snd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean#L34-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean#L34-L35

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply (x : Ambient) (i : Fin 2) :
    (axialEquiv x).2 i = x i.succ := by sorry

attribute [defeq] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
