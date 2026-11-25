-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_exists_toCochain_eq_128651034dbd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_exists_toCochain_eq_128651034dbd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:12:06.445357+00:00
-- url     : https://prove2.me/theorems/a59adce0-9fdd-47ae-b82d-a9053de31b1b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict exists to Cochain eq 128651034dbd: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict exists to Cochain eq 128651034dbd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict exists to Cochain eq 128651034dbd construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict exists to Cochain eq 128651034dbd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L142-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L142-L229

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
set_option maxHeartbeats 1000000

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_exists_toCochain_eq_128651034dbd (F₁ F₂ : SubSystem S x E)
    (hlift : ∀ s : Chart x → E, (∀ I, s I ∈ F₁.sub I) →
      (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ F₂.sub I₂) →
      ∃ t ∈ F₁.secs, ∀ I, t - s I ∈ F₂.sub I)
    (z : Cech.Cochain (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) 0)
    (hz : Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (qres F₁ F₂) 0 z = 0) :
    ∃ t : F₁.secs, toCochain F₁ F₂ t = z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«exists_toCochain_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_exists_toCochain_eq_128651034dbd
