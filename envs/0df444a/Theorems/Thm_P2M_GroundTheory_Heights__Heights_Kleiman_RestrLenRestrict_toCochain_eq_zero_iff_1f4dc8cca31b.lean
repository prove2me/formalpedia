-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toCochain_eq_zero_iff_1f4dc8cca31b
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toCochain_eq_zero_iff_1f4dc8cca31b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:08:44.049307+00:00
-- url     : https://prove2.me/theorems/a7a03b27-2259-49dd-8b6d-b662a3aff5d0
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to Cochain eq zero iff 1f4dc8cca31b: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to Cochain eq zero iff 1f4dc8cca31b
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to Cochain eq zero iff 1f4dc8cca31b construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict to Cochain eq zero iff 1f4dc8cca31b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L102-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L102-L120

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
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type w} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toCochain_eq_zero_iff_1f4dc8cca31b (F₁ F₂ : SubSystem S x E) (t : F₁.secs) :
    toCochain F₁ F₂ t = 0 ↔ t ∈ F₂.secs.comap F₁.secs.subtype := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«toCochain_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_toCochain_eq_zero_iff_1f4dc8cca31b
