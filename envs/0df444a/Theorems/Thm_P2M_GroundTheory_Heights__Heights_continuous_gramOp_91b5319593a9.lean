-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_gramOp_91b5319593a9
-- name    : P2M_GroundTheory_Heights__Heights_continuous_gramOp_91b5319593a9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:06.914991+00:00
-- url     : https://prove2.me/theorems/f3f4484a-4d0c-4c93-b913-b28f7f751913
-- title:
--   P2 M Ground Theory Heights  Heights continuous gram Op 91b5319593a9: P2 M Ground Theory Heights  Heights continuous gram Op 91b5319593a9
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous gram Op 91b5319593a9 construction uses the P2 M Ground Theory Heights  Heights continuous gram Op 91b5319593a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L100-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeJacMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsKernelProjMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeJacMeasurable
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
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_continuous_gramOp_91b5319593a9 (m : ℕ) : Continuous (gramOp (n := n) (m := m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuous_gramOp» := P2M_GroundTheory_Heights__Heights_continuous_gramOp_91b5319593a9
