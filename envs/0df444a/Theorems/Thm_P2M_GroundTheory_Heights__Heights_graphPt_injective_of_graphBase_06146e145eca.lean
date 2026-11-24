-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphPt_injective_of_graphBase_06146e145eca
-- name    : P2M_GroundTheory_Heights__Heights_graphPt_injective_of_graphBase_06146e145eca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:06.087075+00:00
-- url     : https://prove2.me/theorems/31197de2-8fb5-4385-bf64-2948faec43ed
-- title:
--   P2 M Ground Theory Heights  Heights graph Pt injective of graph Base 06146e145eca: P2 M Ground Theory Heights  Heights graph Pt injective of graph Base 06146e145eca
-- statement:
--   The P2 M Ground Theory Heights  Heights graph Pt injective of graph Base 06146e145eca construction uses the P2 M Ground Theory Heights  Heights graph Pt injective of graph Base 06146e145eca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGraphAreaFibre.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsGraphAreaFibre.lean#L24-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
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
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_graphPt_injective_of_graphBase_06146e145eca {d k n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin k)
    (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin k)) : Function.Injective (graphPt e F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«graphPt_injective_of_graphBase» := P2M_GroundTheory_Heights__Heights_graphPt_injective_of_graphBase_06146e145eca
