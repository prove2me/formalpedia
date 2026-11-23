-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ProjPoint_SpecMap_ofHom_eq_away__97605d53820a
-- name    : P2M_GlobalTheory_ProjPoint_SpecMap_ofHom_eq_away__97605d53820a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:32.649649+00:00
-- url     : https://prove2.me/theorems/2ec437f6-88cf-407a-a558-87e272129632
-- title:
--   P2 M Global Theory Proj Point Spec Map of Hom eq away  97605d53820a: P2 M Global Theory Proj Point Spec Map of Hom eq away  97605d53820a
-- statement:
--   The P2 M Global Theory Proj Point Spec Map of Hom eq away  97605d53820a construction uses the P2 M Global Theory Proj Point Spec Map of Hom eq away  97605d53820a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L130-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/AwayLiftCompFromZeroRingHom.lean#L130-L176

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
set_option backward.isDefEq.respectTransparency false

theorem P2M_GlobalTheory_ProjPoint_SpecMap_ofHom_eq_away__97605d53820a (φ : A →+* B) (hφ : (irrelevant 𝒜).toIdeal.map φ = ⊤)
    (ψ : B →+* C) {f : A} {n : ℕ} (hn : 0 < n) (hf : f ∈ 𝒜 n) (hu : IsUnit (ψ (φ f))) :
    Spec.map (CommRingCat.ofHom ψ) ≫ ofHom 𝒜 φ hφ =
      Spec.map (CommRingCat.ofHom (awayLift 𝒜 (ψ.comp φ) f hu)) ≫ Proj.awayι 𝒜 f hf hn := by sorry

alias «GlobalTheory».«ProjPoint».«SpecMap_ofHom_eq_awayι» := P2M_GlobalTheory_ProjPoint_SpecMap_ofHom_eq_away__97605d53820a
