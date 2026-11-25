-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_quotInl_baf1d4324949
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_quotInl_baf1d4324949
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:40.136677+00:00
-- url     : https://prove2.me/theorems/a4425738-7eb0-5522-b7d2-af6aad3c25a9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr quot Inl baf1d4324949: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr quot Inl baf1d432
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr quot Inl baf1d4324949 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr quot Inl baf1d4324949 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L141-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L141-L147

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_quotInl_baf1d4324949 (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₂.sub I ⧸ SubSystem.quotSub F₂ F₃ I) :
    quotPr F₁ F₂ F₃ h32 I (quotInl F₁ F₂ F₃ h21 I m) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«quotPr_quotInl» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_quotInl_baf1d4324949
