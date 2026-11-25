-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_isUnit_mul_mem_idealMod_fbb4e2922bce
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_isUnit_mul_mem_idealMod_fbb4e2922bce
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:57:55.673829+00:00
-- url     : https://prove2.me/theorems/e2309e4a-5da2-521a-8e5b-042cf84b8572
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists is Unit mul mem ideal Mod fbb4e2922bce: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists is Unit mu
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists is Unit mul mem ideal Mod fbb4e2922bce construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term exists is Unit mul mem ideal Mod fbb4e2922bce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L123-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L123-L142

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
  {pp : Ideal (Poly k N)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_isUnit_mul_mem_idealMod_fbb4e2922bce {I K : Chart x} (h : I.1 ⊆ K.1) {a : Ω}
    (ha : a ∈ idealMod pp K) :
    ∃ u : chartRing k x I, IsUnit (chartIncl h u) ∧ (u : Ω) * a ∈ idealMod pp I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«exists_isUnit_mul_mem_idealMod» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_exists_isUnit_mul_mem_idealMod_fbb4e2922bce
