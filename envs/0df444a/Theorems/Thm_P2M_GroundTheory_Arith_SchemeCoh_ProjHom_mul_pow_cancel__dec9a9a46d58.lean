-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_ProjHom_mul_pow_cancel__dec9a9a46d58
-- name    : P2M_GroundTheory_Arith_SchemeCoh_ProjHom_mul_pow_cancel__dec9a9a46d58
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:23.809982+00:00
-- url     : https://prove2.me/theorems/583d4180-8e17-4531-b802-e47b9d2e9c06
-- title:
--   P2 M Ground Theory Arith Scheme Coh Proj Hom mul pow cancel  dec9a9a46d58: P2 M Ground Theory Arith Scheme Coh Proj Hom mul pow cancel  dec9a9a46d58
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Proj Hom mul pow cancel  dec9a9a46d58 construction uses the P2 M Ground Theory Arith Scheme Coh Proj Hom mul pow cancel  dec9a9a46d58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L118-L123

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_TwistingSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ProjHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
universe u
noncomputable section
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
open GroundTheory.Arith.SchemeCoh.ProjHom
variable {X : Scheme.{u}}
variable (f : A →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

theorem P2M_GroundTheory_Arith_SchemeCoh_ProjHom_mul_pow_cancel__dec9a9a46d58 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {v : S}
    {u u' w w' c : R} (hc : IsUnit c) (k d : ℕ) (hu : u' = c ^ d * u) (hw : w' = c ^ (k • d) * w)
    (h : v * φ u' ^ k = φ w') : v * φ u ^ k = φ w := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«ProjHom».«mul_pow_cancel'» := P2M_GroundTheory_Arith_SchemeCoh_ProjHom_mul_pow_cancel__dec9a9a46d58
