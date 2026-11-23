-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolA_integrable_of_cont
-- name    : PositivityTheory.Rg.Sw.LVs.HolA.integrable_of_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:33.61495+00:00
-- url     : https://prove2.me/theorems/f8dc54db-3e8c-45b0-9953-8aaa210121e8
-- title:
--   Hol A: integrable of cont
-- statement:
--   The Hol A construction uses the integrable of cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/HasFDerivAtInt.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/HasFDerivAtInt.lean#L15-L21

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolA
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]

theorem PositivityTheory.Rg.Sw.LVs.HolA.integrable_of_cont {W : Type*} [NormedAddCommGroup W] {f : Kg → W} (hf : Continuous f) :
    Integrable f μ := by sorry
