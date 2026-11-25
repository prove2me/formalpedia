-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_lineNormalDivisorChartAt_1785c42bd7dc
-- name    : P2M_GroundTheory_Heights__Heights_lineNormalDivisorChartAt_1785c42bd7dc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:07.8598+00:00
-- url     : https://prove2.me/theorems/c54c6a1d-b239-4393-a83f-e7b3753d7135
-- title:
--   P2 M Ground Theory Heights  Heights line Normal Divisor Chart At 1785c42bd7dc: P2 M Ground Theory Heights  Heights line Normal Divisor Chart At 1785c42bd7dc
-- statement:
--   The P2 M Ground Theory Heights  Heights line Normal Divisor Chart At 1785c42bd7dc construction uses the P2 M Ground Theory Heights  Heights line Normal Divisor Chart At 1785c42bd7dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDivisorGoodPoint.lean#L51-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDivisorGoodPoint.lean#L51-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
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
open MvPolynomial Filter Topology ComplexSets
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_lineNormalDivisorChartAt_1785c42bd7dc :
    NormalDivisorChartAt IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalModel (fun _ => (1 : ℂ)) 0 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«lineNormalDivisorChartAt» := P2M_GroundTheory_Heights__Heights_lineNormalDivisorChartAt_1785c42bd7dc
