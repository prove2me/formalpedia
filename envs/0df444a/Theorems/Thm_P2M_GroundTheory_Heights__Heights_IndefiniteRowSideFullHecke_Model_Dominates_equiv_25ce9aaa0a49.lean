-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_Dominates_equiv_25ce9aaa0a49
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_Dominates_equiv_25ce9aaa0a49
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:13.469352+00:00
-- url     : https://prove2.me/theorems/2ab910b5-1c73-4621-8d7c-444a6a4896d5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Dominates equiv 25ce9aaa0a49: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Dominates equiv 25ce9aaa
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Dominates equiv 25ce9aaa0a49 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Model Dominates equiv 25ce9aaa0a49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Imports.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/Imports.lean#L8-L11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_Dominates_equiv_25ce9aaa0a49 (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    [Algebra A K] (V : Subring K) :
    GroundTheory.Heights₂.Heights.Model.Dominates A V ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.Dominates A V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Model».«Dominates».«equiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_Dominates_equiv_25ce9aaa0a49
