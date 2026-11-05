-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLevyProcess_continuousOn_levyLocalCharExponent
-- name    : ProbabilityTheory.IsLevyProcess.continuousOn_levyLocalCharExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:06:52.532544+00:00
-- url     : https://prove2.me/theorems/35f0290c-00b1-4e0c-89ea-3726897f122b
-- title:
--   LeanLevy: ProbabilityTheory.IsLevyProcess.continuousOn_levyLocalCharExponent
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L248

import Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Defs.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
open Filter MeasureTheory Topology
open scoped NNReal
universe u v

theorem ProbabilityTheory.IsLevyProcess.continuousOn_levyLocalCharExponent {Ω : Sort (u + 1)} [MeasurableSpace Ω] {E : Sort (v + 1)} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E] {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ] (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    ContinuousOn (h.levyLocalCharExponent hX) (h.levyGoodDomain hX) := by sorry
