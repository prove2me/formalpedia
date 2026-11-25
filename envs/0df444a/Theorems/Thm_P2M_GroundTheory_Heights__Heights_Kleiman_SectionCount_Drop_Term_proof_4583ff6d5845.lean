-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_proof_4583ff6d5845
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_proof_4583ff6d5845
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:58:52.413611+00:00
-- url     : https://prove2.me/theorems/6b59284c-77bc-5f6e-a031-861c65595aaa
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term proof 4583ff6d5845: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term proof 4583ff6d5845
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term proof 4583ff6d5845 construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop Term proof 4583ff6d5845 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L328-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDropTerm.lean#L328-L439

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_proof_4583ff6d5845 (hGA : GeneratedAmple.Statement.{u, w}) (hFin : QuotSectionsFinite.Statement.{u, w}) :
    SectionCount.Drop.Term.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«Term».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_Term_proof_4583ff6d5845
