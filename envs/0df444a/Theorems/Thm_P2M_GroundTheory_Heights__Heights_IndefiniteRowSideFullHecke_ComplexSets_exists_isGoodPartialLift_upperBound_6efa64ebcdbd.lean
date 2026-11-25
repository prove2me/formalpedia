-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_upperBound_6efa64ebcdbd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_upperBound_6efa64ebcdbd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:55.736128+00:00
-- url     : https://prove2.me/theorems/ada1d132-7569-4529-90b5-70c9137be781
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists is Good Partial Lift upper Bound 6efa64ebcdbd: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists is Good Partial Lift upper Bound 6efa64ebcdbd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists is Good Partial Lift upper Bound 6efa64ebcdbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothPartialLifts.lean#L24-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPerfectFieldExtensionFormallySmoothPartialLifts.lean#L24-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothFrobeniusLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPerfectFieldExtensionFormallySmoothPartialLifts
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_upperBound_6efa64ebcdbd {p : ℕ} {N : Ideal B} {u : K →ₐ[F] B ⧸ N} {ψ : K →+* B}
    (c : Set {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ})
    (hc : IsChain (fun a b => PartialLiftLE a.1 b.1) c) (hne : c.Nonempty) :
    ∃ ub : {σ : Σ L : IntermediateField F K, L →ₐ[F] B // IsGoodPartialLift p N u ψ σ},
      ∀ a ∈ c, PartialLiftLE a.1 ub.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_isGoodPartialLift_upperBound» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_isGoodPartialLift_upperBound_6efa64ebcdbd
