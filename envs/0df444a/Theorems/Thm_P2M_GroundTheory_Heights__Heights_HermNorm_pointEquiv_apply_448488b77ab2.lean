-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_pointEquiv_apply_448488b77ab2
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_pointEquiv_apply_448488b77ab2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:23.813439+00:00
-- url     : https://prove2.me/theorems/212b2131-c06a-5e39-9021-0a80ce09a887
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm point Equiv apply 448488b77ab2: P2 M Ground Theory Heights  Heights Herm Norm point Equiv apply 448488b77ab2
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm point Equiv apply 448488b77ab2 construction uses the P2 M Ground Theory Heights  Heights Herm Norm point Equiv apply 448488b77ab2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L23-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeKrullDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentDim
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
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_pointEquiv_apply_448488b77ab2 (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.pointEquiv y = h.pointOf y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«pointEquiv_apply» := P2M_GroundTheory_Heights__Heights_HermNorm_pointEquiv_apply_448488b77ab2
