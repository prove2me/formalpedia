-- Prove2me | Theorems.Thm_ProbabilityTheory_measurable_rightLimWithin
-- name    : ProbabilityTheory.measurable_rightLimWithin
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:06:52.677172+00:00
-- url     : https://prove2.me/theorems/4ce10476-76a3-4c93-9948-8d3349b70fa8
-- title:
--   measurable rightLimWithin
-- statement:
--   The source theorem `ProbabilityTheory.measurable_rightLimWithin` is extracted from `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F000

/-
Copyright (c) 2026 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rohit Manokaran, Rémy Degenne
-/

/-! # Cadlag modification of quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section CountableEvents

variable [OrderBot ι] {T : Set ι} {t : ι}

end CountableEvents

section RegularitySet

variable [OrderBot ι]

variable [TopologicalSpace ι] [OrderTopology ι]

end RegularitySet

variable [TopologicalSpace ι] [OrderBot ι] [OrderTopology ι]
  --[FirstCountableTopology ι] -- required for ∀ t : ι, (𝓝[>] t).IsCountablyGenerated
  [DenselyOrdered ι] [NoMaxOrder ι] -- required for ∀ t : ι, (𝓝[>] t).NeBot)

/-! ### Pathwise regularization

For a fixed path `h : ι → ℝ` admitting one-sided limits along a dense set `T`, the right-limit
regularization `r` is right-continuous and inherits the left limits of `h`. -/

section PathRegularization

variable {T : Set ι} {h r : ι → ℝ} {x : ι}

end PathRegularization

/-! ### Uncountable sets accumulate from the right -/

section Accumulation

end Accumulation

open Function

omit [OrderBot ι] [DenselyOrdered ι] [NoMaxOrder ι] in
theorem _root_.ProbabilityTheory.measurable_rightLimWithin [FirstCountableTopology ι]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) (t : ι) :
    Measurable (fun ω ↦ rightLimWithin (X · ω) T t) := by sorry
