-- Prove2me | Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_ProjHom_corr_fromOfGlobalSections__ce9e3ee9af8b
-- name    : P2M_GroundTheory_Arith_SchemeCoh_ProjHom_corr_fromOfGlobalSections__ce9e3ee9af8b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:29:19.008079+00:00
-- url     : https://prove2.me/theorems/718c48e7-91a2-41e0-a330-6c72f5c54232
-- title:
--   P2 M Ground Theory Arith Scheme Coh Proj Hom corr from Of Global Sections  ce9e3ee9af8b: P2 M Ground Theory Arith Scheme Coh Proj Hom corr from Of Global Sections  ce9e3ee9af8b
-- statement:
--   The P2 M Ground Theory Arith Scheme Coh Proj Hom corr from Of Global Sections  ce9e3ee9af8b construction uses the P2 M Ground Theory Arith Scheme Coh Proj Hom corr from Of Global Sections  ce9e3ee9af8b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/ProjHom.lean#L77-L83

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

theorem P2M_GroundTheory_Arith_SchemeCoh_ProjHom_corr_fromOfGlobalSections__ce9e3ee9af8b {r : A} {d : ℕ} (hd : 0 < d) (hr : r ∈ 𝒜 d) (V : X.Opens)
    (hV : X.basicOpen (f r) = V) (h : V ≤ Proj.fromOfGlobalSections 𝒜 f hf ⁻¹ᵁ Proj.basicOpen 𝒜 r)
    (k : ℕ) (a : A) (ha : a ∈ 𝒜 (k • d)) :
    corr 𝒜 (Proj.fromOfGlobalSections 𝒜 f hf) r V h (Away.mk 𝒜 hr k a ha) *
      V.ι.appTop (f r) ^ k = V.ι.appTop (f a) := by sorry

alias «GroundTheory».«Arith».«SchemeCoh».«ProjHom».«corr_fromOfGlobalSections'» := P2M_GroundTheory_Arith_SchemeCoh_ProjHom_corr_fromOfGlobalSections__ce9e3ee9af8b
