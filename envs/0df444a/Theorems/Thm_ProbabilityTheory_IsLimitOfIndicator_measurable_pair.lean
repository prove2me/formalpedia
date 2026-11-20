-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLimitOfIndicator_measurable_pair
-- name    : ProbabilityTheory.IsLimitOfIndicator.measurable_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:58:04.875036+00:00
-- url     : https://prove2.me/theorems/a684dcf8-1c30-47e2-b8e6-022ede3b974e
-- title:
--   measurable pair
-- statement:
--   The source theorem `ProbabilityTheory.IsLimitOfIndicator.measurable_pair` is extracted from `BrownianMotion.Continuity.LimitModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002

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

theorem _root_.ProbabilityTheory.IsLimitOfIndicator.measurable_pair
    {T : Type*} [PseudoEMetricSpace T] [SecondCountableTopology T]
    [MeasurableSpace E] [BorelSpace E]
    {Y X Z X' : T → Ω → E} {U₁ U₂ : Set T}
    (hX : ∀ t, Measurable (X t)) (hX' : ∀ t, Measurable (X' t))
    (hX_pair : ∀ i j, Measurable[_, borel (E × E)] fun ω ↦ (X i ω, X' j ω))
    (hY : IsLimitOfIndicator Y X P U₁) (hZ : IsLimitOfIndicator Z X' P U₂)
    (s t : T) :
    Measurable[_, borel (E × E)] (fun ω ↦ (Y s ω, Z t ω)) := by sorry
