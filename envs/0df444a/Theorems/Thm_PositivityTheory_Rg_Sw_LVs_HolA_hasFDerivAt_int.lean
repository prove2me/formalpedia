-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolA_hasFDerivAt_int
-- name    : PositivityTheory.Rg.Sw.LVs.HolA.hasFDerivAt_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:57:29.820513+00:00
-- url     : https://prove2.me/theorems/111aa158-e458-42b6-9b5a-6b16023f7c87
-- title:
--   Hol A: has FDeriv At int
-- statement:
--   The Hol A construction uses the has FDeriv At int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/HasFDerivAtInt.lean#L23-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/HasFDerivAtInt.lean#L23-L47

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

theorem PositivityTheory.Rg.Sw.LVs.HolA.hasFDerivAt_int {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    {Ω : Set E} (hΩ : IsOpen Ω) {Φ : Kg → E → W} {Φ' : Kg → E → (E →L[ℂ] W)}
    (hc : ContinuousOn (fun y : Kg × E => Φ y.1 y.2) (univ ×ˢ Ω))
    (hc' : ContinuousOn (fun y : Kg × E => Φ' y.1 y.2) (univ ×ˢ Ω))
    (hd : ∀ k, ∀ x ∈ Ω, HasFDerivAt (Φ k) (Φ' k x) x) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ k, Φ k x ∂μ) (∫ k, Φ' k x₀ ∂μ) x₀ := by sorry
