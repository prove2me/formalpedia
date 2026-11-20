-- Prove2me | Theorems.Thm_ProbabilityTheory_rightContModif_ae_eq_of_tendstoInMeasure
-- name    : ProbabilityTheory.rightContModif_ae_eq_of_tendstoInMeasure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:47:23.957039+00:00
-- url     : https://prove2.me/theorems/bdda92ac-580d-45cd-8e20-796d0858f7f4
-- title:
--   rightContModif ae eq of tendstoInMeasure
-- statement:
--   The source theorem `ProbabilityTheory.rightContModif_ae_eq_of_tendstoInMeasure` is extracted from `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_CadlagModification_F002

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

/-! ## Right-continuous modification of a quasimartingale

For a real quasimartingale `X` we define a process `rightContModif X` with the following properties:
* `rightContModif X` is right-continuous
* `rightContModif X` has left limits almost everywhere
* for all `t` outside a countable set, `rightContModif X t =ᵐ[μ] X t`
* if `X` is right-continuous in probability, then `rightContModif X` is a modification of `X`.
* if the filtration is right-continuous, then `rightContModif X` is adapted.

Note that if `X` is not right-continuous in probability, we can still obtain a modification by
changing the value of `rightContModif X` on a countable set of times, with the drawback that the
right-continuity then holds only outside that countable set.

-/

theorem _root_.ProbabilityTheory.rightContModif_ae_eq_of_tendstoInMeasure [SecondCountableTopology ι] [IsFiniteMeasure μ]
    (hX : IsRealQuasimartingale 𝓕 X μ)
    (t : ι) (hXRC : TendstoInMeasure μ X (𝓝[>] t) (X t)) :
    rightContModif X t =ᵐ[μ] X t := by sorry
