-- Prove2me | Theorems.Thm_UniformContinuousOn_exists_tendsto
-- name    : UniformContinuousOn.exists_tendsto
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:40:06.793072+00:00
-- url     : https://prove2.me/theorems/dfeb819f-4abf-4324-b627-2a0dec9de535
-- title:
--   exists tendsto
-- statement:
--   The source theorem `UniformContinuousOn.exists_tendsto` is extracted from `BrownianMotion.Continuity.KolmogorovChentsov`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Definitions.Def_BrownianMotion_Auxiliary_Topology_F001
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_Gaussian_StochasticProcesses_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

theorem UniformContinuousOn.exists_tendsto {α β : Type*} [UniformSpace α] [FirstCountableTopology α]
    [UniformSpace β] [CompleteSpace β] {s t : Set α} (hs : Dense s) (ht : IsOpen t)
    {f : s → β} (hf : UniformContinuousOn f {x | ↑x ∈ t}) (a : α) (ha : a ∈ t) :
    ∃ c, Tendsto f (comap Subtype.val (𝓝 a)) (𝓝 c) := by sorry
