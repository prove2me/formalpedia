-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_twistSys_sub_zero_37c528144722
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_twistSys_sub_zero_37c528144722
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:59:12.615063+00:00
-- url     : https://prove2.me/theorems/494464b8-b318-592a-869a-bdf7e78c8651
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term twist Sys sub zero 37c528144722: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term twist Sys sub zero 37c528144722
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term twist Sys sub zero 37c528144722 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term twist Sys sub zero 37c528144722 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L316-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L316-L319

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_twistSys_sub_zero_37c528144722 (I : Chart x) : (twistSys k x 0).sub I = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«twistSys_sub_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_twistSys_sub_zero_37c528144722
