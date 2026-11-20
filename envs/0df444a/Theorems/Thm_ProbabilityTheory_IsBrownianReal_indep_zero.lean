-- Prove2me | Theorems.Thm_ProbabilityTheory_IsBrownianReal_indep_zero
-- name    : ProbabilityTheory.IsBrownianReal.indep_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:52:38.443119+00:00
-- url     : https://prove2.me/theorems/1201a66f-911d-4e2a-8697-4ea4250aa7fa
-- title:
--   indep zero
-- statement:
--   The source theorem `ProbabilityTheory.IsBrownianReal.indep_zero` is extracted from `BrownianMotion.Gaussian.BrownianMotion`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Gaussian_BrownianMotion_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Brownian motion

-/

@[expose] public section

open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

namespace Finset

/-! ### Indexing the elements of a finset in order -/

variable [LinearOrder T] (I : Finset T)

section Bot

variable [Bot T]

end Bot

end Finset

namespace ProbabilityTheory

section Increments

/-! ### Independent increments -/

end Increments

section IsPreBrownianReal

variable (X : ℝ≥0 → Ω → ℝ)

variable {X} {P : Measure Ω}

end IsPreBrownianReal

section IsBrownianReal

variable (X : ℝ≥0 → Ω → ℝ)

variable {X}

theorem _root_.ProbabilityTheory.IsBrownianReal.indep_zero (h : IsBrownianReal X P) (hX : ∀ t, Measurable (X t))
    (hX' : ∀ ω, Continuous (X · ω)) {A : Set Ω}
    (hA : MeasurableSet[⨅ s > 0, natural X (fun t ↦ (hX t).stronglyMeasurable) s] A) :
    P A = 0 ∨ P A = 1 := by sorry
