-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_hdeg_subsingleton_d600335fc570
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_hdeg_subsingleton_d600335fc570
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:57:41.336592+00:00
-- url     : https://prove2.me/theorems/4823d145-955b-49d1-bd58-1b025bf36b14
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity hdeg subsingleton d600335fc570: P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity hdeg subsingleton d60033
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity hdeg subsingleton d600335fc570 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Quotient Additivity hdeg subsingleton d600335fc570 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperQuotAdd.lean#L78-L86

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
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] (G : Cell U → Type v)
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_hdeg_subsingleton_d600335fc570 {R' : Type*} [CommRing R'] [∀ I, Module R' (G I)] (deg : ∀ I, Submodule R' (G I))
    (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R'] G J) (i : ℕ) [IsEmpty (Cech.Idx U i)] :
    Subsingleton (Cech.Hdeg G deg ρ' i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperQuotientAdditivity».«hdeg_subsingleton» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotientAdditivity_hdeg_subsingleton_d600335fc570
