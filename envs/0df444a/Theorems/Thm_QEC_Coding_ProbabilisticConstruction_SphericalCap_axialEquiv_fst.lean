-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:48:32.991887+00:00
-- url     : https://prove2.me/theorems/c6e6519b-fbdf-4702-80be-43b31fab670a
-- title:
--   Spherical Cap: axial Equiv fst
-- statement:
--   The Spherical Cap construction uses the axial Equiv fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean#L32-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean#L32-L32

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst (x : Ambient) : (axialEquiv x).1 = x 0 := by sorry

attribute [defeq] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
