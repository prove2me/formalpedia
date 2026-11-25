-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_surjective_05066ea6fa37
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_surjective_05066ea6fa37
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:46.050341+00:00
-- url     : https://prove2.me/theorems/35ec070f-fa29-5964-a2ec-56df3e792f05
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr surjective 05066ea6fa37: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr surjective 0506
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr surjective 05066ea6fa37 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Pr surjective 05066ea6fa37 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L157-L161

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_surjective_05066ea6fa37 (F₁ F₂ F₃ : SubSystem k x E) (h32 : ∀ I, F₃.sub I ≤ F₂.sub I) (I : Chart x) :
    Function.Surjective (quotPr F₁ F₂ F₃ h32 I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«quotPr_surjective» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotPr_surjective_05066ea6fa37
