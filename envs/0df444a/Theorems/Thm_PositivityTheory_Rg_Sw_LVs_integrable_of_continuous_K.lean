-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_integrable_of_continuous_K
-- name    : PositivityTheory.Rg.Sw.LVs.integrable_of_continuous_K
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:48.045805+00:00
-- url     : https://prove2.me/theorems/ee14999f-6d95-4897-9fbb-bb9a7fc1fd08
-- title:
--   LVs: integrable of continuous K
-- statement:
--   The LVs construction uses the integrable of continuous K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/IteratedFDerivMulConstOf.lean#L166-L169

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem PositivityTheory.Rg.Sw.LVs.integrable_of_continuous_K {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] {f : Kg → ℂ} (hf : Continuous f) :
    Integrable f μ := by sorry
