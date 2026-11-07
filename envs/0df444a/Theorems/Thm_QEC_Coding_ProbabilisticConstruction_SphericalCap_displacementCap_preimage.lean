-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_displacementCap_preimage
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.displacementCap_preimage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:51:46.829814+00:00
-- url     : https://prove2.me/theorems/d5f4452e-66aa-4284-a2a7-d15d23cf68d1
-- title:
--   Spherical Cap: displacement Cap preimage
-- statement:
--   The Spherical Cap construction uses the displacement Cap preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L158-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L158-L163

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.displacementCap_preimage {R : ℝ} (hR : 0 < R) (u : Sphere) (c : ℝ) :
    (fun s : Sphere => R • (s : Space)) ⁻¹' displacementCap R u c = cap u c := by sorry
