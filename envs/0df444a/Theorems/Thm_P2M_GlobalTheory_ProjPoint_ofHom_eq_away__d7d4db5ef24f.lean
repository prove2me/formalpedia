-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ProjPoint_ofHom_eq_away__d7d4db5ef24f
-- name    : P2M_GlobalTheory_ProjPoint_ofHom_eq_away__d7d4db5ef24f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:17.594108+00:00
-- url     : https://prove2.me/theorems/d5794660-6a78-4bf7-8fe9-ac2b3f3bc139
-- title:
--   P2 M Global Theory Proj Point of Hom eq away  d7d4db5ef24f: P2 M Global Theory Proj Point of Hom eq away  d7d4db5ef24f
-- statement:
--   The P2 M Global Theory Proj Point of Hom eq away  d7d4db5ef24f construction uses the P2 M Global Theory Proj Point of Hom eq away  d7d4db5ef24f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L178-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L178-L181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.ProjPoint
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {B C : Type u} [CommRing B] [CommRing C]

theorem P2M_GlobalTheory_ProjPoint_ofHom_eq_away__d7d4db5ef24f (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    {f : A} {n : ℕ} (hn : 0 < n) (hf : f ∈ 𝒜 n) (hu : IsUnit (φ f)) :
    ofHom 𝒜 φ hφ = Spec.map (CommRingCat.ofHom (awayLift 𝒜 φ f hu)) ≫ Proj.awayι 𝒜 f hf hn := by sorry

alias «GlobalTheory».«ProjPoint».«ofHom_eq_awayι» := P2M_GlobalTheory_ProjPoint_ofHom_eq_away__d7d4db5ef24f
