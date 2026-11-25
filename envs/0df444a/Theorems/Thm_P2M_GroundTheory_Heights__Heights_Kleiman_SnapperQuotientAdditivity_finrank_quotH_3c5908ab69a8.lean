-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_finrank_quotH_3c5908ab69a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_finrank_quotH_3c5908ab69a8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:43.398117+00:00
-- url     : https://prove2.me/theorems/0a189ba0-efdc-4937-85c3-b88b5ebbbd72
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity finrank quot H 3c5908ab69a8: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity finrank quot H 3c5908ab69a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity finrank quot H 3c5908ab69a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity finrank quot H 3c5908ab69a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L163-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L163-L167

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_finrank_quotH_3c5908ab69a8 (F₁ F₂ : SubSystem k x E) (i : ℕ) :
    Module.finrank k (SubSystem.quotH F₁ F₂ i) =
      Module.finrank k (Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) (fun _ => ⊤)
        (SubSystem.quotRes F₁ F₂) i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«finrank_quotH» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_finrank_quotH_3c5908ab69a8
