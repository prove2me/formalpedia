-- Prove2me | Theorems.Thm_ProbabilityTheory_adapted_rightLimWithin
-- name    : ProbabilityTheory.adapted_rightLimWithin
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:08:43.497178+00:00
-- url     : https://prove2.me/theorems/391b8c17-7936-4731-858a-418952a81f74
-- title:
--   adapted rightLimWithin
-- statement:
--   The source theorem `ProbabilityTheory.adapted_rightLimWithin` is extracted from `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_LeftLimWithin_F000
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_StochasticIntegral_Cadlag_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Predictable_F000
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F002
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F003
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

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

omit [OrderBot ι] in
theorem _root_.ProbabilityTheory.adapted_rightLimWithin [FirstCountableTopology ι] [𝓕.IsRightContinuous]
    {T : Set ι} (hT : T.Countable) (hX : Adapted 𝓕 X) :
    Adapted 𝓕 (fun t ω ↦ rightLimWithin (X · ω) T t) := by sorry
