-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_mk_cd742c972719
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_mk_cd742c972719
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:11:11.527817+00:00
-- url     : https://prove2.me/theorems/62ef3b86-5ce5-559c-b223-cede6fcc1008
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict d mk cd742c972719: P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict d mk cd742c972719
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict d mk cd742c972719 construction uses the P2 M Ground Theory Heights  Heights Kleiman Restr Len Restrict d mk cd742c972719 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L122-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrLenRestrict.lean#L122-L138

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_mk_cd742c972719 (F₁ F₂ : SubSystem S x E) (u : Cech.Idx (support x) 0 → E) (hu : ∀ I, u I ∈ F₁.sub I.1)
    (J : Cech.Idx (support x) 1) :
    Cech.d (fun I => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (qres F₁ F₂) 0
        (fun I => Submodule.Quotient.mk ⟨u I, hu I⟩) J =
      Submodule.Quotient.mk ⟨∑ j : J.1.1, Cech.sgn J.1.1 j • u (Cech.face J j),
        Submodule.sum_mem _ fun j _ =>
          zsmul_mem (F₁.mono _ _ (Cech.face_subset J j) _ (hu (Cech.face J j))) _⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«RestrLenRestrict».«d_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_RestrLenRestrict_d_mk_cd742c972719
