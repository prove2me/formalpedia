-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_ker_coneJacMat_f32e4b3739d8
-- name    : P2M_GroundTheory_Heights__Heights_mem_ker_coneJacMat_f32e4b3739d8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:50:19.0968+00:00
-- url     : https://prove2.me/theorems/8a13fbdd-93e5-5179-9c57-5748cba56ab3
-- title:
--   P2 M Ground Theory Heights  Heights mem ker cone Jac Mat f32e4b3739d8: P2 M Ground Theory Heights  Heights mem ker cone Jac Mat f32e4b3739d8
-- statement:
--   The P2 M Ground Theory Heights  Heights mem ker cone Jac Mat f32e4b3739d8 construction uses the P2 M Ground Theory Heights  Heights mem ker cone Jac Mat f32e4b3739d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L27-L36

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

theorem P2M_GroundTheory_Heights__Heights_mem_ker_coneJacMat_f32e4b3739d8 (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y v : EuclideanSpace ℂ (Fin n)) :
    v ∈ LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) ↔
      ∀ i, ∑ j, eval (h.pointOf y) (pderiv j (g i)) * h.pointOf v j = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_ker_coneJacMat» := P2M_GroundTheory_Heights__Heights_mem_ker_coneJacMat_f32e4b3739d8
