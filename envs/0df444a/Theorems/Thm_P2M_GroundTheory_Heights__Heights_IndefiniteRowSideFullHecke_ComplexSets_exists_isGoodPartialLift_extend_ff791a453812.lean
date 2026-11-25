-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_extend_ff791a453812
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_extend_ff791a453812
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:12.27981+00:00
-- url     : https://prove2.me/theorems/a09d2e76-1787-44df-b60a-42fb551b7198
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists is Good Partial Lift extend ff791a453812: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists is Good Partial Lift extend ff791a453812 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists is Good Partial Lift extend ff791a453812 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothExtensionStep.lean#L11-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothExtensionStep.lean#L11-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothPartialLifts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothExtensionStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Polynomial IntermediateField
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
variable {F K B : Type*} [Field F] [Field K] [Algebra F K] [CommRing B] [Algebra F B]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_extend_ff791a453812 (p : ℕ) [hp : Fact p.Prime] [CharP K p] {N : Ideal B}
    {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B} (hψ : ∀ (z : K) (c : B), Ideal.Quotient.mk N c = u z → ψ z = c ^ p)
    {L : IntermediateField F K} {φ : L →ₐ[F] B} (hgood : IsGoodPartialLift p N u ψ ⟨L, φ⟩) {x : K}
    (hx : x ∉ L) :
    ∃ σ : Σ L : IntermediateField F K, L →ₐ[F] B,
      IsGoodPartialLift p N u ψ σ ∧ PartialLiftLE ⟨L, φ⟩ σ ∧ x ∈ σ.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_isGoodPartialLift_extend» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_extend_ff791a453812
