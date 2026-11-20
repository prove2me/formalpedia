-- Prove2me | Theorems.Thm_ProbabilityTheory_measureReal_exists_abs_lt_le
-- name    : ProbabilityTheory.measureReal_exists_abs_lt_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:18:23.061293+00:00
-- url     : https://prove2.me/theorems/7a2eea56-1eaf-4ff0-9da5-b0de88e141a8
-- title:
--   measureReal exists abs lt le
-- statement:
--   The source theorem `ProbabilityTheory.measureReal_exists_abs_lt_le` is extracted from `BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Filtration_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F000
import Definitions.Def_BrownianMotion_Auxiliary_Upcrossing_F001
import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_Basic_F000

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohit Manokaran, Rémy Degenne
-/

/-! # Maximal inequality for real quasimartingales -/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory.SimpleProcess

namespace ProbabilityTheory

variable {ι Ω : Type*} [LinearOrder ι]
  {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ι mΩ} {μ : Measure Ω}
  {X : ι → Ω → ℝ} {τ σ : Ω → WithTop ι} {i : ι}

section Bridge

variable {F : Finset ι} {t : ι} {k l : ℕ}

end Bridge

/-! ### Upcrossing and alternation bounds along finite time sets -/

section UpcrossingBound

variable {a b : ℝ} {t : ι} {F : Finset ι} {m : ℕ}

end UpcrossingBound

/-! ### Selection of alternating tuples from frequent oscillation -/

section Selection

variable [TopologicalSpace ι] [OrderTopology ι]

variable {T : Set ι} {x d : ι} {a b : ℝ} {ω : Ω}

end Selection

/-! ### Maximal inequality along finite time sets -/

section Maximal

variable {t : ι} {F : Finset ι} {lam : ℝ}

-- todo name

theorem _root_.ProbabilityTheory.measureReal_exists_abs_lt_le [OrderBot ι] [IsFiniteMeasure μ]
    (hX : StronglyAdapted 𝓕 X) (hXint : ∀ s, Integrable (X s) μ) {C : ℝ}
    (hC : ∀ S : ElementaryPredictableSet 𝓕, μ[(S.indicator (1 : ℝ) ● X) t] ≤ C)
    (hlam : 0 < lam) (hF : ∀ s ∈ F, s ≤ t) :
    μ.real {ω | ∃ s ∈ F, lam < |X s ω|}
      ≤ 2 * (C + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ + ∫ ω, |X t ω| ∂μ) / lam := by sorry
