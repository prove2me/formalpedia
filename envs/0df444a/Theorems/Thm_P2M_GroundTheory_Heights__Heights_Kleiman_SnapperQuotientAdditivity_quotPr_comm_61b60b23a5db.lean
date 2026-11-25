-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_comm_61b60b23a5db
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_comm_61b60b23a5db
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:28.419807+00:00
-- url     : https://prove2.me/theorems/4a58d3ae-e170-49a4-a5d5-856921c81fcf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr comm 61b60b23a5db: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr comm 61b60b23a5db
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr comm 61b60b23a5db construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr comm 61b60b23a5db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L124-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L124-L128

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_comm_61b60b23a5db (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I J : Chart x) (h : I.1 ⊆ J.1)
    (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I) :
    quotPr F₁ F₂ F₃ h32 J (SubSystem.quotRes F₁ F₃ I J h m) =
      SubSystem.quotRes F₁ F₂ I J h (quotPr F₁ F₂ F₃ h32 I m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«quotPr_comm» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_comm_61b60b23a5db
