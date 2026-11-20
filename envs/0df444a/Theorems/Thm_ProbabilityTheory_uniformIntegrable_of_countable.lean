-- Prove2me | Theorems.Thm_ProbabilityTheory_uniformIntegrable_of_countable
-- name    : ProbabilityTheory.uniformIntegrable_of_countable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:04:31.476457+00:00
-- url     : https://prove2.me/theorems/eff7de61-d944-4a15-8b17-3b934ba58e50
-- title:
--   uniformIntegrable of countable
-- statement:
--   The source theorem `ProbabilityTheory.uniformIntegrable_of_countable` is extracted from `BrownianMotion.StochasticIntegral.Quasimartingale.CadlagModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.ProbabilityTheory.uniformIntegrable_of_countable [IsFiniteMeasure μ] (hX : IsRealQuasimartingale 𝓕 X μ)
    (hT : T.Countable) :
    UniformIntegrable (fun s : (T ∩ Set.Iic t : Set ι) ↦ X s) 1 μ := by sorry
