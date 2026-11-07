-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axisReflection_measurePreserving
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.axisReflection_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:55:20.161405+00:00
-- url     : https://prove2.me/theorems/df7df7d1-307d-48f7-b3ab-54313f6f4775
-- title:
--   Spherical Cap: axis Reflection measure Preserving
-- statement:
--   The Spherical Cap construction uses the axis Reflection measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean#L49-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean#L49-L51

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.axisReflection_measurePreserving (u v : Ambient) :
    MeasurePreserving (axisReflection u v) volume volume := by sorry
