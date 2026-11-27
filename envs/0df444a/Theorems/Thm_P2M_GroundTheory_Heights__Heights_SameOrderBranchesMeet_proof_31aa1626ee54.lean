-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SameOrderBranchesMeet_proof_31aa1626ee54
-- name    : P2M_GroundTheory_Heights__Heights_SameOrderBranchesMeet_proof_31aa1626ee54
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:06:38.861584+00:00
-- url     : https://prove2.me/theorems/ce0b30d1-e430-4172-9671-7166959ad4e8
-- title:
--   P2 M Ground Theory Heights  Heights Same Order Branches Meet proof 31aa1626ee54: P2 M Ground Theory Heights  Heights Same Order Branches Meet proof 31aa1626ee54
-- statement:
--   The P2 M Ground Theory Heights  Heights Same Order Branches Meet proof 31aa1626ee54 construction uses the P2 M Ground Theory Heights  Heights Same Order Branches Meet proof 31aa1626ee54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrderBranchesMeet.lean#L43-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSameOrderBranchesMeet.lean#L43-L79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrderBranchesMeet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInCurveComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrderBranchesMeet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelExists_proof_269d895ff472

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology

theorem P2M_GroundTheory_Heights__Heights_SameOrderBranchesMeet_proof_31aa1626ee54 (hC : BranchInCurveComponent.Statement) (hO : SameOrdersLiftCentre.Statement)
    (hL : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement) : SameOrderBranchesMeet.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SameOrderBranchesMeet».«proof» := P2M_GroundTheory_Heights__Heights_SameOrderBranchesMeet_proof_31aa1626ee54
