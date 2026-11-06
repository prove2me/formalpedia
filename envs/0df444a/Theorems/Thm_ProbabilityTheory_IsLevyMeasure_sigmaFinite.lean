-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
-- name    : ProbabilityTheory.IsLevyMeasure.sigmaFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:42:35.202998+00:00
-- url     : https://prove2.me/theorems/d01bf43a-c0e3-450e-9623-6763ae7474e0
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyMeasure.sigmaFinite
-- statement:
--   Every Lévy measure is σ-finite. Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyMeasure.lean#L106

import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Order.Basic

theorem ProbabilityTheory.IsLevyMeasure.sigmaFinite : ∀ {ν : @MeasureTheory.Measure Real Real.measurableSpace},
  ProbabilityTheory.IsLevyMeasure ν → @MeasureTheory.SigmaFinite Real Real.measurableSpace ν := by sorry
