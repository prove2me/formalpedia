-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_ProjHom_isUnit___appTop_b013236f49ec
-- name    : P2M_GroundTheory_Arith_SchemeCoh_ProjHom_isUnit___appTop_b013236f49ec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:39:15.076633+00:00
-- url     : https://prove2.me/theorems/ce0f773e-44d8-4bb7-89f8-bcde12f59fea
-- title:
--   P2 M Ground Theory Arith Scheme Coh Proj Hom is Unit   app Top b013236f49ec: P2 M Ground Theory Arith Scheme Coh Proj Hom is Unit   app Top b013236f49ec
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Proj Hom is Unit   app Top b013236f49ec construction uses the P2 M Ground Theory Arith Scheme Coh Proj Hom is Unit   app Top b013236f49ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L105-L109

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

theorem P2M_GroundTheory_Arith_SchemeCoh_ProjHom_isUnit___appTop_b013236f49ec (x : Γ(X, ⊤)) : IsUnit ((X.basicOpen x).ι.appTop x) := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«ProjHom».«isUnit_ι_appTop» := P2M_GroundTheory_Arith_SchemeCoh_ProjHom_isUnit___appTop_b013236f49ec
