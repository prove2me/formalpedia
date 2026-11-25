-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_pow_mem_twistSys_30d864c5f0c8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_pow_mem_twistSys_30d864c5f0c8
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:33.005179+00:00
-- url     : https://prove2.me/theorems/9f5b63a0-dac5-5a7b-8433-e2013ac5e063
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term pow mem twist Sys 30d864c5f0c8: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term pow mem twist Sys 30d864c5f0c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term pow mem twist Sys 30d864c5f0c8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term pow mem twist Sys 30d864c5f0c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L321-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L321-L324

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_pow_mem_twistSys_30d864c5f0c8 (j : Fin (N + 1)) (m : ℕ) (I : Chart x) :
    x j ^ m ∈ (twistSys k x (m : ℤ)).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«pow_mem_twistSys» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_pow_mem_twistSys_30d864c5f0c8
