-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_eq_zero_iff_4b1e54951f8f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_eq_zero_iff_4b1e54951f8f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:26.395289+00:00
-- url     : https://prove2.me/theorems/98e51e30-5013-4e77-8abb-4328d1e0f223
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to H0 Of Cocycle eq zero iff 4b1e54951f8f: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to H0 Of Cocycle eq zero iff 4b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to H0 Of Cocycle eq zero iff 4b1e54951f8f construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to H0 Of Cocycle eq zero iff 4b1e54951f8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L31-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrLenRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type w}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {M : Type w} [AddCommGroup M] [Module R M]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_eq_zero_iff_4b1e54951f8f (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0) (m : M) :
    toH0OfCocycle φ hφ m = 0 ↔ φ m = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«toH0OfCocycle_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_eq_zero_iff_4b1e54951f8f
