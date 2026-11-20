-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLimitOfIndicator_measurable
-- name    : ProbabilityTheory.IsLimitOfIndicator.measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:56:52.009277+00:00
-- url     : https://prove2.me/theorems/45d64d65-69ab-43ae-95c3-e9c4818329cf
-- title:
--   measurable
-- statement:
--   The source theorem `ProbabilityTheory.IsLimitOfIndicator.measurable` is extracted from `BrownianMotion.Continuity.LimitModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F001

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
#

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : T → Ω → E} {c : ℝ≥0∞}
  {U : Set T}

section IndicatorProcess

variable {A : Set Ω} [hE : Nonempty E]

end IndicatorProcess

variable [PseudoEMetricSpace E] [hE : Nonempty E]
  [TopologicalSpace T] [SecondCountableTopology T]

theorem _root_.ProbabilityTheory.IsLimitOfIndicator.measurable [MeasurableSpace E] [BorelSpace E] {Y X : T → Ω → E}
    (hX : ∀ t, Measurable (X t)) (hY : IsLimitOfIndicator Y X P U) (t : T) :
    Measurable (Y t) := by sorry
