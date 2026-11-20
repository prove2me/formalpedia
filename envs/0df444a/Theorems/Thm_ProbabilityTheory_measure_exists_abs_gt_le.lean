-- Prove2me | Theorems.Thm_ProbabilityTheory_measure_exists_abs_gt_le
-- name    : ProbabilityTheory.measure_exists_abs_gt_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:19:15.471589+00:00
-- url     : https://prove2.me/theorems/ba4c0370-4b88-4fdb-b316-d670700ce14f
-- title:
--   measure exists abs gt le
-- statement:
--   The source theorem `ProbabilityTheory.measure_exists_abs_gt_le` is extracted from `BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_StochasticIntegral_Quasimartingale_MaximalInequality_F002

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

end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

theorem _root_.ProbabilityTheory.measure_exists_abs_gt_le [IsFiniteMeasure μ] {ε : ℝ}
    (hX : IsRealQuasimartingale 𝓕 X μ) (hε : 0 < ε) (hT : T.Countable) :
    μ {ω | ∃ s ∈ T ∩ Set.Iic t, ε < |X s ω|}
      ≤ ENNReal.ofReal (2 * (variationBound X 𝓕 μ t + ∫ ω, |X t ω - X ⊥ ω| ∂μ + ∫ ω, |X ⊥ ω| ∂μ
          + ∫ ω, |X t ω| ∂μ) / ε) := by sorry
