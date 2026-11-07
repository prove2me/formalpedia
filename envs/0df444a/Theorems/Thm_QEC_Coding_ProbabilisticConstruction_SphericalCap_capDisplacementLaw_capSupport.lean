-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_capDisplacementLaw_capSupport
-- name    : QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_capSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:38:03.139713+00:00
-- url     : https://prove2.me/theorems/1a6c35b5-9bb1-4b53-bc49-4eadd281bac0
-- title:
--   Spherical Cap: cap Displacement Law cap Support
-- statement:
--   The Spherical Cap construction uses the cap Displacement Law cap Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L165-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/SphericalCap/Measure.lean#L165-L168

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

theorem QEC.Coding.ProbabilisticConstruction.SphericalCap.capDisplacementLaw_capSupport {R c : ℝ} (hR : 0 < R) (u : Sphere) (hc : c < 1) :
    capDisplacementLaw R u c (displacementCap R u c) = 1 := by sorry
