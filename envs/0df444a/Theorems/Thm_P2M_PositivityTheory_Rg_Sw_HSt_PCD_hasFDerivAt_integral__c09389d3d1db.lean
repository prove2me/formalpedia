-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Sw_HSt_PCD_hasFDerivAt_integral__c09389d3d1db
-- name    : P2M_PositivityTheory_Rg_Sw_HSt_PCD_hasFDerivAt_integral__c09389d3d1db
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:55.870093+00:00
-- url     : https://prove2.me/theorems/f931a04a-eee6-5756-b6fe-b179dcea6dd0
-- title:
--   P2 M Positivity Theory Rg Sw HSt PCD has FDeriv At integral  c09389d3d1db: P2 M Positivity Theory Rg Sw HSt PCD has FDeriv At integral  c09389d3d1db
-- statement:
--   The P2 M Positivity Theory Rg Sw HSt PCD has FDeriv At integral  c09389d3d1db construction uses the P2 M Positivity Theory Rg Sw HSt PCD has FDeriv At integral  c09389d3d1db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L169-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/CayleyCosetSums/ParamCD.lean#L169-L181

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_ParamCD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.PCD
variable {F X : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X] [SecondCountableTopology X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set F} {K : F → X → E}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {Ω : Set F}

theorem P2M_PositivityTheory_Rg_Sw_HSt_PCD_hasFDerivAt_integral__c09389d3d1db (hΩ : IsOpen Ω) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (k : F × V → E)
    (hk : ContDiffOn ℝ ∞ k (Ω ×ˢ univ)) (v : X → V) (hv : Continuous v) (h : X → ℂ) (hh : Continuous h)
    (hsupp : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ C : Set X, IsCompact C ∧ ∀ x' ∈ W, ∀ u ∉ C, k (x', v u) = 0) {x : F} (hx : x ∈ Ω) :
    HasFDerivAt (fun x => ∫ u, h u • k (x, v u) ∂ν) (∫ u, h u • fderiv ℝ (fun x' => k (x', v u)) x ∂ν) x := by sorry

alias «PositivityTheory».«Rg».«Sw».«HSt».«PCD».«hasFDerivAt_integral'» := P2M_PositivityTheory_Rg_Sw_HSt_PCD_hasFDerivAt_integral__c09389d3d1db
