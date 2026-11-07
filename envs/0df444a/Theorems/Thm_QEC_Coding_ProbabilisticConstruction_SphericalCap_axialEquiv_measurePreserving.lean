-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_measurePreserving
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:53:12.049471+00:00
-- url     : https://prove2.me/theorems/2c2e30e2-fb3c-48d0-908f-f9630f690a65
-- title:
--   Spherical Cap: axial Equiv measure Preserving
-- statement:
--   The Spherical Cap construction uses the axial Equiv measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean#L26-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/AxialCoordinates.lean#L26-L30

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_measurePreserving :
    MeasurePreserving axialEquiv volume (volume.prod volume) := by sorry
