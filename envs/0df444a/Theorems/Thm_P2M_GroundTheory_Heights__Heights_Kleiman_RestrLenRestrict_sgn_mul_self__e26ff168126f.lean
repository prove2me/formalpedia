-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_sgn_mul_self__e26ff168126f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_sgn_mul_self__e26ff168126f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:34.114636+00:00
-- url     : https://prove2.me/theorems/209d1ea0-4c3c-4051-835f-bc8f019253ba
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict sgn mul self  e26ff168126f: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict sgn mul self  e26ff168126f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict sgn mul self  e26ff168126f construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict sgn mul self  e26ff168126f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L58-L60

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_sgn_mul_self__e26ff168126f (L : Finset (Fin n)) (j : Fin n) : Cech.sgn L j * Cech.sgn L j = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«sgn_mul_self'» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_sgn_mul_self__e26ff168126f
