-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_toCochain_b5411ff145ec
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_toCochain_b5411ff145ec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:11:17.71932+00:00
-- url     : https://prove2.me/theorems/7d39b493-4f49-5493-97ed-21886054f08d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict d to Cochain b5411ff145ec: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict d to Cochain b5411ff145ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict d to Cochain b5411ff145ec construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict d to Cochain b5411ff145ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L87-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L87-L92

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_toCochain_b5411ff145ec (F₁ F₂ : SubSystem S x E) (t : F₁.secs) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (qres F₁ F₂) 0
      (toCochain F₁ F₂ t) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«d_toCochain» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_toCochain_b5411ff145ec
