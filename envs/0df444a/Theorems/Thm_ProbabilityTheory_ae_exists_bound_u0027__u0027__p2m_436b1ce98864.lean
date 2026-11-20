-- Prove2me | Theorems.Thm_ProbabilityTheory_ae_exists_bound_u0027__u0027__p2m_436b1ce98864
-- name    : ProbabilityTheory.ae_exists_bound_u0027__u0027__p2m_436b1ce98864
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:20:38.052455+00:00
-- url     : https://prove2.me/theorems/b0dbaa42-0ec2-4153-95ef-b3c57cf5aabd
-- title:
--   ae exists bound''
-- statement:
--   The source theorem `ProbabilityTheory.ae_exists_bound''` is extracted from `BrownianMotion.StochasticIntegral.Quasimartingale.MaximalInequality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

end Maximal

/-! ## Maximal inequality for countable sets -/

section CountableEvents

variable {T : Set ι} {t : ι} {a b lam : ℝ} {m : ℕ}

variable [OrderBot ι]

theorem _root_.ProbabilityTheory.ae_exists_bound_u0027__u0027__p2m_436b1ce98864 [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) (t : ι) :
    ∀ᵐ ω ∂μ, ∃ M : ℕ, ∀ s' ∈ T ∩ Set.Iic t, |X s' ω| ≤ M + 1 := by sorry
