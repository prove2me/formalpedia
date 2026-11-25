-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_SmoothIntegrals_contDiffOn_integral_nat
-- name    : PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_integral_nat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:45.707486+00:00
-- url     : https://prove2.me/theorems/f95a1d3e-ae95-57fe-b4fc-29c3bbd320dc
-- title:
--   Smooth Integrals: cont Diff On integral nat
-- statement:
--   The Smooth Integrals construction uses the cont Diff On integral nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PSmoothA.lean#L83-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PSmoothA.lean#L83-L107

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

theorem PositivityTheory.Rg.BcB.CG.SmoothIntegrals.contDiffOn_integral_nat (hU : IsOpen U) (hW : IsOpen W) (hp : Continuous p) (hpW : ∀ y, p y ∈ W) (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : X × M → V),
      ContDiffOn ℝ ∞ Q (U ×ˢ W) → (∀ x ∈ U, ∃ K, IsCompact K ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ K, Q (x', p y) = 0) →
      ContDiffOn ℝ n (fun x => ∫ y, Q (x, p y) ∂μ) U := by sorry
