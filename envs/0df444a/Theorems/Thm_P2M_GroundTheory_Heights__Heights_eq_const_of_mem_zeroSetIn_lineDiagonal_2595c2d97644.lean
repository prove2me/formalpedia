-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eq_const_of_mem_zeroSetIn_lineDiagonal_2595c2d97644
-- name    : P2M_GroundTheory_Heights__Heights_eq_const_of_mem_zeroSetIn_lineDiagonal_2595c2d97644
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:45:51.020135+00:00
-- url     : https://prove2.me/theorems/f7b3c0ee-7b9c-4b58-bfb3-a6833520a322
-- title:
--   P2 M Ground Theory Heights  Heights eq const of mem zero Set In line Diagonal 2595c2d97644: P2 M Ground Theory Heights  Heights eq const of mem zero Set In line Diagonal 2595c2d97644
-- statement:
--   The P2 M Ground Theory Heights  Heights eq const of mem zero Set In line Diagonal 2595c2d97644 construction uses the P2 M Ground Theory Heights  Heights eq const of mem zero Set In line Diagonal 2595c2d97644 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDivisorGoodPoint.lean#L36-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDivisorGoodPoint.lean#L36-L49

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

theorem P2M_GroundTheory_Heights__Heights_eq_const_of_mem_zeroSetIn_lineDiagonal_2595c2d97644 {z : Fin 1 ⊕ Fin 1 → ℂ}
    (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn IndefiniteRowSideFullHecke.ComplexSets.lineDiagonalIdeal) :
    z = fun _ => z (Sum.inl 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eq_const_of_mem_zeroSetIn_lineDiagonal» := P2M_GroundTheory_Heights__Heights_eq_const_of_mem_zeroSetIn_lineDiagonal_2595c2d97644
