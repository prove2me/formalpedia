-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotRes_comp_b9c0a60636d5
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotRes_comp_b9c0a60636d5
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:16.285122+00:00
-- url     : https://prove2.me/theorems/e1c97bb6-624a-4e9c-836e-e72471a9f54a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Res comp b9c0a60636d5: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Res comp b9c0a60636d5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Res comp b9c0a60636d5 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity quot Res comp b9c0a60636d5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L113-L116

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotRes_comp_b9c0a60636d5 (F₁ F₂ : SubSystem k x E) (I J K : Chart x) (hIJ : I.1 ⊆ J.1) (hJK : J.1 ⊆ K.1) :
    (SubSystem.quotRes F₁ F₂ J K hJK).comp (SubSystem.quotRes F₁ F₂ I J hIJ) =
      SubSystem.quotRes F₁ F₂ I K (hIJ.trans hJK) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«quotRes_comp» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_quotRes_comp_b9c0a60636d5
