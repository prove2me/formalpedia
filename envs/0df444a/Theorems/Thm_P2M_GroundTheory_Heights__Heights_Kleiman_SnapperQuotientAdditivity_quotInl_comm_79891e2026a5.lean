-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotInl_comm_79891e2026a5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotInl_comm_79891e2026a5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:40.058444+00:00
-- url     : https://prove2.me/theorems/62833393-00af-4261-8ec7-ac181b1a0c02
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Inl comm 79891e2026a5: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Inl comm 79891e2026a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Inl comm 79891e2026a5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Inl comm 79891e2026a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L118-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotAddSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSubquotFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperQuotAdd
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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotientAdditivity
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotInl_comm_79891e2026a5 (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotInl F₁ F₂ F₃ h21 J (SubSystem.quotRes F₂ F₃ I J h m) =
      SubSystem.quotRes F₁ F₃ I J h (quotInl F₁ F₂ F₃ h21 I m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«quotInl_comm» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotInl_comm_79891e2026a5
