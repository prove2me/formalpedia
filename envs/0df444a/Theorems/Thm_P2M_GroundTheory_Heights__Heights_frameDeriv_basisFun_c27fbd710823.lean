-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_frameDeriv_basisFun_c27fbd710823
-- name    : P2M_GroundTheory_Heights__Heights_frameDeriv_basisFun_c27fbd710823
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:46:34.622791+00:00
-- url     : https://prove2.me/theorems/b7024a37-c363-4b36-b324-b7959499c62a
-- title:
--   P2 M Ground Theory Heights  Heights frame Deriv basis Fun c27fbd710823: P2 M Ground Theory Heights  Heights frame Deriv basis Fun c27fbd710823
-- statement:
--   The P2 M Ground Theory Heights  Heights frame Deriv basis Fun c27fbd710823 construction uses the P2 M Ground Theory Heights  Heights frame Deriv basis Fun c27fbd710823 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L36-L38

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

theorem P2M_GroundTheory_Heights__Heights_frameDeriv_basisFun_c27fbd710823 (j : Fin n) (g : MvPolynomial (Fin n) ℂ) :
    frameDeriv (EuclideanSpace.basisFun (Fin n) ℂ) j g = pderiv j g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«frameDeriv_basisFun» := P2M_GroundTheory_Heights__Heights_frameDeriv_basisFun_c27fbd710823
