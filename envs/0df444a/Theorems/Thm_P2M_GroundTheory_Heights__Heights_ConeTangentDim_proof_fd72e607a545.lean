-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTangentDim_proof_fd72e607a545
-- name    : P2M_GroundTheory_Heights__Heights_ConeTangentDim_proof_fd72e607a545
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:19.090378+00:00
-- url     : https://prove2.me/theorems/b9e31625-927d-420b-bb78-09d438e0cd46
-- title:
--   P2 M Ground Theory Heights  Heights Cone Tangent Dim proof fd72e607a545: P2 M Ground Theory Heights  Heights Cone Tangent Dim proof fd72e607a545
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Tangent Dim proof fd72e607a545 construction uses the P2 M Ground Theory Heights  Heights Cone Tangent Dim proof fd72e607a545 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L103-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L103-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeKrullDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeTangentDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralLine_proof_ffc40bccdc87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_proof_0af09eb068df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeMassOfFibre_proof_e2b8f0be35c4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeTangentAverage_proof_3157c23abeec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointLine_proof_60a02c7c6efe

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

theorem P2M_GroundTheory_Heights__Heights_ConeTangentDim_proof_fd72e607a545 (hDim : ConeKrullDimLe.Statement) (hNull : NullSmaller.Statement)
    (hJac : FrameJacobianGeneric.Statement) : ConeTangentDim.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeTangentDim».«proof» := P2M_GroundTheory_Heights__Heights_ConeTangentDim_proof_fd72e607a545
