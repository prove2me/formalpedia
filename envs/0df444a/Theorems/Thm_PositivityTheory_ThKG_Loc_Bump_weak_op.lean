-- Prove2me | Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_weak_op
-- name    : PositivityTheory.ThKG.Loc.Bump.weak_op
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:40.665381+00:00
-- url     : https://prove2.me/theorems/c10d9eb3-bd79-48ee-a91c-f854644846ae
-- title:
--   Bump: weak op
-- statement:
--   The Bump construction uses the weak op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L177-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/ArchimedeanBumps/SliceAn.lean#L177-L202

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IteratedFDerivSubApply
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_SliceAn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped SchwartzMap NNReal
variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

theorem PositivityTheory.ThKG.Loc.Bump.weak_op {α : Type} [MeasurableSpace α] (μ : Measure α) (G : α → 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ))
    (hex : ∀ f, ∃ g : 𝓢(V₁, ℂ), ∀ T : 𝓢(V₁, ℂ) →L[ℂ] ℂ, Integrable (fun a => T (G a f)) μ ∧ T g = ∫ a, T (G a f) ∂μ)
    (hb : ∀ k j : ℕ, ∃ (p : Seminorm ℂ 𝓢(V, ℂ)) (h : α → ℝ), Continuous p ∧ Integrable h μ ∧
      ∀ a f, SchwartzMap.seminorm ℂ k j (G a f) ≤ p f * h a) :
    ∃ L : 𝓢(V, ℂ) →L[ℂ] 𝓢(V₁, ℂ), ∀ f (T : 𝓢(V₁, ℂ) →L[ℂ] ℂ), Integrable (fun a => T (G a f)) μ ∧ T (L f) = ∫ a, T (G a f) ∂μ := by sorry
