-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_isClosed_coneSet_ab7a54df5c4b
-- name    : P2M_GroundTheory_Heights__Heights_isClosed_coneSet_ab7a54df5c4b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:51.325848+00:00
-- url     : https://prove2.me/theorems/07aa08f4-a9c5-471a-9b1c-e7efc8b513ff
-- title:
--   P2 M Ground Theory Heights  Heights is Closed cone Set ab7a54df5c4b: P2 M Ground Theory Heights  Heights is Closed cone Set ab7a54df5c4b
-- statement:
--   The P2 M Ground Theory Heights  Heights is Closed cone Set ab7a54df5c4b construction uses the P2 M Ground Theory Heights  Heights is Closed cone Set ab7a54df5c4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentAverage.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentAverage.lean#L34-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_isClosed_coneSet_ab7a54df5c4b {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (coneSet h J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«isClosed_coneSet» := P2M_GroundTheory_Heights__Heights_isClosed_coneSet_ab7a54df5c4b
