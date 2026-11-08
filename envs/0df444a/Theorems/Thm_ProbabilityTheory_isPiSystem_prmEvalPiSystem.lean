-- Prove2me | Theorems.Thm_ProbabilityTheory_isPiSystem_prmEvalPiSystem
-- name    : ProbabilityTheory.isPiSystem_prmEvalPiSystem
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:49:42.435727+00:00
-- url     : https://prove2.me/theorems/371591b6-28dd-4ec5-986e-126584bb74ed
-- title:
--   LeanLevy: ProbabilityTheory.isPiSystem_prmEvalPiSystem
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section variables are declared in the preamble. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonFiltration.lean#L140

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E}

theorem ProbabilityTheory.isPiSystem_prmEvalPiSystem {R : Set E} : IsPiSystem (prmEvalPiSystem K X m R) := by sorry
