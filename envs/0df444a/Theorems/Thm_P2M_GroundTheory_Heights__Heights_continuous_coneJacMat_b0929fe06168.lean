-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_coneJacMat_b0929fe06168
-- name    : P2M_GroundTheory_Heights__Heights_continuous_coneJacMat_b0929fe06168
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:12.116799+00:00
-- url     : https://prove2.me/theorems/75f4d1f9-09e3-4f7b-858a-6116bd45b9ed
-- title:
--   P2 M Ground Theory Heights  Heights continuous cone Jac Mat b0929fe06168: P2 M Ground Theory Heights  Heights continuous cone Jac Mat b0929fe06168
-- statement:
--   The P2 M Ground Theory Heights  Heights continuous cone Jac Mat b0929fe06168 construction uses the P2 M Ground Theory Heights  Heights continuous cone Jac Mat b0929fe06168 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L20-L25

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

theorem P2M_GroundTheory_Heights__Heights_continuous_coneJacMat_b0929fe06168 (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ) :
    Continuous (coneJacMat h g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«continuous_coneJacMat» := P2M_GroundTheory_Heights__Heights_continuous_coneJacMat_b0929fe06168
