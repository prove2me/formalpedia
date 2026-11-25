-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_quotMul_res_b337987bbe92
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_quotMul_res_b337987bbe92
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:46.453336+00:00
-- url     : https://prove2.me/theorems/20568588-6d68-50b2-8d19-5bc1baf8bfe6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term quot Mul res b337987bbe92: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term quot Mul res b337987bbe92
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term quot Mul res b337987bbe92 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term quot Mul res b337987bbe92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L261-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L261-L267

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotSectionsFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDropTerm
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
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.SectionCount GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop GroundTheory.Heights₂.Heights.Kleiman.SectionCount.Drop.Term
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_quotMul_res_b337987bbe92 (F₁ G₁ F₂ G₂ : SubSystem k x Ω) (s : Ω) (hF : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ F₂.sub I)
    (hG : ∀ I, ∀ y ∈ F₁.sub I, y ∈ G₁.sub I → s * y ∈ G₂.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₁.sub I ⧸ SubSystem.quotSub F₁ G₁ I) :
    quotMul F₁ G₁ F₂ G₂ s hF hG J (SubSystem.quotRes F₁ G₁ I J h m) =
      SubSystem.quotRes F₂ G₂ I J h (quotMul F₁ G₁ F₂ G₂ s hF hG I m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«quotMul_res» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_quotMul_res_b337987bbe92
