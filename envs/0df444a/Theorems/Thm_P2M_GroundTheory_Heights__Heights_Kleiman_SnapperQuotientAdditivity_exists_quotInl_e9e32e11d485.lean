-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_exists_quotInl_e9e32e11d485
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_exists_quotInl_e9e32e11d485
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:07:51.905529+00:00
-- url     : https://prove2.me/theorems/db0ef862-651b-4886-b517-b33e987e8a07
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity exists quot Inl e9e32e11d485: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity exists quot Inl e9e32e11d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity exists quot Inl e9e32e11d485 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity exists quot Inl e9e32e11d485 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L149-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L149-L155

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_exists_quotInl_e9e32e11d485 (F₁ F₂ F₃ : SubSystem k x E) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I)
    (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) (m : F₁.sub I ⧸ SubSystem.quotSub F₁ F₃ I)
    (hm : quotPr F₁ F₂ F₃ h32 I m = 0) : ∃ y, quotInl F₁ F₂ F₃ h21 I y = m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«exists_quotInl» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_exists_quotInl_e9e32e11d485
