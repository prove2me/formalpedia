-- Prove2me | Theorems.Thm_ProbabilityTheory_norm_charFun_map_sub_le
-- name    : ProbabilityTheory.norm_charFun_map_sub_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:30:26.688906+00:00
-- url     : https://prove2.me/theorems/4631ccb7-5187-45de-a782-33c39902a4cf
-- title:
--   LeanLevy small-jump characteristic-function helper: norm_charFun_map_sub_le
-- statement:
--   Original private LeanLevy TimeSpacePoisson proof helper promoted into owner-private Prove2Me theorem to establish the compensated small-jump characteristic function.

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_LeanLevy_RandomMeasure_PoissonCompensated
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal
variable {Ω : Type} [MeasurableSpace Ω]
  {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem ProbabilityTheory.norm_charFun_map_sub_le [IsProbabilityMeasure μ] {V W : Ω → ℝ}
    (hV : AEMeasurable V μ) (hW : AEMeasurable W μ)
    (hVW : Integrable (fun ω => V ω - W ω) μ) (ξ : ℝ) :
    ‖charFun (μ.map V) ξ - charFun (μ.map W) ξ‖ ≤ |ξ| * ∫ ω, |V ω - W ω| ∂μ := by sorry
