-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_SmoothIntegrals_contDiffOn_integral
-- name    : PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_integral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:47.381109+00:00
-- url     : https://prove2.me/theorems/bcf1dd97-5176-424f-a0b4-bb035cb0c44c
-- title:
--   Smooth Integrals: cont Diff On integral
-- statement:
--   The Smooth Integrals construction uses the cont Diff On integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PSmoothA.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PSmoothA.lean#L109-L113

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PSmoothA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.CG.SmoothIntegrals
variable {X M T : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [TopologicalSpace T] [T2Space T] [MeasurableSpace T] [OpensMeasurableSpace T]
variable {μ : Measure T} [IsFiniteMeasureOnCompacts μ] {U : Set X} {W : Set M} {p : T → M}

theorem PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_integral (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Q : X × M → V}
    (hQ : ContDiffOn ℝ ∞ Q (U ×ˢ W)) (hs : ∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ y, Q (x, p y) ∂μ) U := by sorry
