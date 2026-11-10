-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat26b_smearedMeasure_finite_public
-- name    : ProbabilityTheory.leanlevy_chat26b_smearedMeasure_finite_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:48:04.182318+00:00
-- url     : https://prove2.me/theorems/46fc3adf-ab78-4d0d-a673-c421a5cd828f
-- title:
--   Public finite smeared Levy-Khintchine measure
-- statement:
--   The Gaussian atom and sinc-deficit Levy jump density have finite total mass, so the smeared canonical Levy measure is finite.
-- source:
--   slink/LeanLevy 7e73fd9b, LevyKhintchineUniqueness.lean lines104-112, canonical original 4e893400 Proved candidate31976.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat26b_smearedMeasure_finite_public (σ_sq : ℝ≥0)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    IsFiniteMeasure (smearedMeasure σ_sq ν) := by sorry
