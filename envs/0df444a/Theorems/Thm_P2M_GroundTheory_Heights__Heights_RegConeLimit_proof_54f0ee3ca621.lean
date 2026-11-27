-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegConeLimit_proof_54f0ee3ca621
-- name    : P2M_GroundTheory_Heights__Heights_RegConeLimit_proof_54f0ee3ca621
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:35:14.229446+00:00
-- url     : https://prove2.me/theorems/6ea9145b-d73f-4bb2-a24a-078f81e14168
-- title:
--   P2 M Ground Theory Heights  Heights Reg Cone Limit proof 54f0ee3ca621: P2 M Ground Theory Heights  Heights Reg Cone Limit proof 54f0ee3ca621
-- statement:
--   The P2 M Ground Theory Heights  Heights Reg Cone Limit proof 54f0ee3ca621 construction uses the P2 M Ground Theory Heights  Heights Reg Cone Limit proof 54f0ee3ca621 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegConeLimit.lean#L80-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegConeLimit.lean#L80-L120

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ConeBall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeFsLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegConeLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeFsLogIntegrable_proof_f583b043a7ab

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
open MvPolynomial MeasureTheory Filter Topology Set ConeFsLog
noncomputable section
open RegConeLimit

theorem P2M_GroundTheory_Heights__Heights_RegConeLimit_proof_54f0ee3ca621 (hFin : ConeBallFinite.Statement) (hInt : ConeFsLogIntegrable.Statement)
    (hNull : ConeHyperplaneNull.Statement) : RegConeLimit.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RegConeLimit».«proof» := P2M_GroundTheory_Heights__Heights_RegConeLimit_proof_54f0ee3ca621
