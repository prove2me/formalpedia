-- Prove2me | Theorems.Thm_ProbabilityTheory_countable_not_rightLimWithin_ae_eq
-- name    : ProbabilityTheory.countable_not_rightLimWithin_ae_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:10:18.597222+00:00
-- url     : https://prove2.me/theorems/fbc6f239-502e-4081-804a-4bdfb4c9f8d5
-- title:
--   countable not rightLimWithin ae eq
-- statement:
--   The source theorem `ProbabilityTheory.countable_not_rightLimWithin_ae_eq` is extracted from `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F001

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

theorem _root_.ProbabilityTheory.countable_not_rightLimWithin_ae_eq [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    {T : Set ι} (hTc : T.Countable) (hTd : Dense T) :
    {t | ¬ (fun ω ↦ rightLimWithin (X · ω) T t) =ᵐ[μ] X t}.Countable := by sorry
