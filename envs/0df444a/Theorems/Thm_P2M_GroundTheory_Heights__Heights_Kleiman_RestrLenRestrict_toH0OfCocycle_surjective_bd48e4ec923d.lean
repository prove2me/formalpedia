-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_surjective_bd48e4ec923d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_surjective_bd48e4ec923d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:56.586668+00:00
-- url     : https://prove2.me/theorems/c3f910a0-135a-5ab2-8cda-75dd568903cd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to H0 Of Cocycle surjective bd48e4ec923d: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to H0 Of Cocycle surjective bd48
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to H0 Of Cocycle surjective bd48e4ec923d construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to H0 Of Cocycle surjective bd48e4ec923d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L38-L47

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_surjective_bd48e4ec923d (φ : M →ₗ[R] Cech.Cochain G 0) (hφ : ∀ m, Cech.d G ρ 0 (φ m) = 0)
    (h : ∀ z : Cech.Cochain G 0, Cech.d G ρ 0 z = 0 → ∃ m, φ m = z) : Function.Surjective (toH0OfCocycle φ hφ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«toH0OfCocycle_surjective» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toH0OfCocycle_surjective_bd48e4ec923d
