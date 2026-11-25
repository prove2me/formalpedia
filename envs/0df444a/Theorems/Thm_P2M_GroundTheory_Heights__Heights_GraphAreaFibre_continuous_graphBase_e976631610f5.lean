-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaFibre_continuous_graphBase_e976631610f5
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaFibre_continuous_graphBase_e976631610f5
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:18:38.950075+00:00
-- url     : https://prove2.me/theorems/0946374b-28c3-4bc8-baf9-c5f234d617a1
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Fibre continuous graph Base e976631610f5: P2 M Ground Theory Heights  Heights Graph Area Fibre continuous graph Base e976631610f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Fibre continuous graph Base e976631610f5 construction uses the P2 M Ground Theory Heights  Heights Graph Area Fibre continuous graph Base e976631610f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGraphAreaFibre.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGraphAreaFibre.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaMultiplicityWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGraphAreaFibre
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
open MeasureTheory Module Set
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_GraphAreaFibre_continuous_graphBase_e976631610f5 {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k) :
    Continuous (graphBase e : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin d)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaFibre».«continuous_graphBase» := P2M_GroundTheory_Heights__Heights_GraphAreaFibre_continuous_graphBase_e976631610f5
