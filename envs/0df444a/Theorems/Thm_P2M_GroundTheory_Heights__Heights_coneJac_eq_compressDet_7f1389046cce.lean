-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneJac_eq_compressDet_7f1389046cce
-- name    : P2M_GroundTheory_Heights__Heights_coneJac_eq_compressDet_7f1389046cce
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:48:31.307154+00:00
-- url     : https://prove2.me/theorems/f83f1e8a-7952-58fa-ba78-fd5a40eaa88a
-- title:
--   P2 M Ground Theory Heights  Heights cone Jac eq compress Det 7f1389046cce: P2 M Ground Theory Heights  Heights cone Jac eq compress Det 7f1389046cce
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Jac eq compress Det 7f1389046cce construction uses the P2 M Ground Theory Heights  Heights cone Jac eq compress Det 7f1389046cce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L121-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L121-L125

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

theorem P2M_GroundTheory_Heights__Heights_coneJac_eq_compressDet_7f1389046cce (hComp : TangentJacCompress.Statement) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) {m : ℕ} (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    coneJac h J π y = compressDet π (coneTangent h J y).starProjection := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneJac_eq_compressDet» := P2M_GroundTheory_Heights__Heights_coneJac_eq_compressDet_7f1389046cce
