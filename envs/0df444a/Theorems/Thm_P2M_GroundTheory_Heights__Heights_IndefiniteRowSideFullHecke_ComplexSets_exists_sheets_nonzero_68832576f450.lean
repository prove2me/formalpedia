-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_sheets_nonzero_68832576f450
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_sheets_nonzero_68832576f450
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:52.582856+00:00
-- url     : https://prove2.me/theorems/48e9fc94-2d67-4f06-853a-fcc23ce14b8f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists sheets nonzero 68832576f450: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exis
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists sheets nonzero 68832576f450 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists sheets nonzero 68832576f450 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L177-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PWeaklyHolomorphicIntegral.lean#L177-L234

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeaklyHolomorphicIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeaklyHolomorphicIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_sheets_nonzero_68832576f450 {σ : Type} [Fintype σ] {k m : ℕ} (Z W : Set (σ → ℂ))
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (G : (σ → ℂ) → ℂ) (O Q : Set (Fin k → ℂ))
    (s : Fin m → (Fin k → ℂ) → σ → ℂ) (hWo : IsOpen W) (hOo : IsOpen O) (hQo : IsOpen Q) (hQO : Q ⊆ O)
    (hQne : Q.Nonempty) (hsd : ∀ j, DifferentiableOn ℂ (s j) O)
    (hsO : ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∩ W ∧ A (s j y') = y') ∧ Function.Injective (fun j => s j y') ∧
      ∀ z ∈ Z ∩ W, A z = y' → z ∈ Set.range (fun j => s j y'))
    (hGc : ContinuousOn G W) (hnd : ∀ z ∈ Z ∩ W, ∀ V ∈ 𝓝 z, ∃ x ∈ Z ∩ V, G x ≠ 0) :
    ∃ y ∈ Q, ∀ j, G (s j y) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_sheets_nonzero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_sheets_nonzero_68832576f450
