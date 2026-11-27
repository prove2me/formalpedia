-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegMassNearSmall_proof_2e152794035e
-- name    : P2M_GroundTheory_Heights__Heights_RegMassNearSmall_proof_2e152794035e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:35:08.160789+00:00
-- url     : https://prove2.me/theorems/0e18068c-d032-5c0b-91a0-416db53c1479
-- title:
--   P2 M Ground Theory Heights  Heights Reg Mass Near Small proof 2e152794035e: P2 M Ground Theory Heights  Heights Reg Mass Near Small proof 2e152794035e
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Mass Near Small proof 2e152794035e construction uses the P2 M Ground Theory Heights  Heights Reg Mass Near Small proof 2e152794035e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegMassNearSmall.lean#L13-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegMassNearSmall.lean#L13-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegMassNearSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarIntAdd_proof_5f0bc402ccc8

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

theorem P2M_GroundTheory_Heights__Heights_RegMassNearSmall_proof_2e152794035e (hCmp : RegFormCompare.Statement) (hBall : RegBallMass.Statement)
    (hCov : SmallSetBallCover.Statement) : RegMassNearSmall.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegMassNearSmall».«proof» := P2M_GroundTheory_Heights__Heights_RegMassNearSmall_proof_2e152794035e
