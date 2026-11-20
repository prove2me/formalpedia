-- Prove2me | Theorems.Thm_ProbabilityTheory_ContinuousMap_borel_eq_iSup_comap_eval
-- name    : ProbabilityTheory.ContinuousMap.borel_eq_iSup_comap_eval
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:54:50.92573+00:00
-- url     : https://prove2.me/theorems/125d47af-140f-4e16-9ea2-122d923d1e5f
-- title:
--   borel eq iSup comap eval
-- statement:
--   The source theorem `ProbabilityTheory.ContinuousMap.borel_eq_iSup_comap_eval` is extracted from `BrownianMotion.Gaussian.BrownianMotion`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Gaussian_BrownianMotion_F001

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

end IsBrownianReal

-- for blueprint

-- for blueprint

section Measure

section ContinuousMap.MeasurableSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open TopologicalSpace in
theorem _root_.ProbabilityTheory.ContinuousMap.borel_eq_iSup_comap_eval [SecondCountableTopology X] [SecondCountableTopology Y]
    [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y] :
    borel C(X, Y) = ⨆ a : X, (borel Y).comap fun b ↦ b a := by sorry
