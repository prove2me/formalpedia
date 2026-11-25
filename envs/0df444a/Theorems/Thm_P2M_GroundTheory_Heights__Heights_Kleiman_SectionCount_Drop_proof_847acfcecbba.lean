-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_proof_847acfcecbba
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_proof_847acfcecbba
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:38:09.819676+00:00
-- url     : https://prove2.me/theorems/724ea68a-1c66-4c59-b333-fc56d06a24bc
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Section Count Drop proof 847acfcecbba: P2 M Ground Theory Heights  Heights Kleiman Section Count Drop proof 847acfcecbba
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Section Count Drop proof 847acfcecbba construction uses the P2 M Ground Theory Heights  Heights Kleiman Section Count Drop proof 847acfcecbba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDrop.lean#L109-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountDrop.lean#L109-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropTermSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountDropHilbWSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountDrop
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
open Filter
universe u w
open Classical

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_proof_847acfcecbba (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionCount».«Drop».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionCount_Drop_proof_847acfcecbba
