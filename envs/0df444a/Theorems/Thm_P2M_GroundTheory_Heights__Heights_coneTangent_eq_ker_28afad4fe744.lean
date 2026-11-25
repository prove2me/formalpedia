-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneTangent_eq_ker_28afad4fe744
-- name    : P2M_GroundTheory_Heights__Heights_coneTangent_eq_ker_28afad4fe744
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:46:22.715863+00:00
-- url     : https://prove2.me/theorems/bc8c6a07-955d-45b0-8778-18fdab1f3b48
-- title:
--   P2 M Ground Theory Heights  Heights cone Tangent eq ker 28afad4fe744: P2 M Ground Theory Heights  Heights cone Tangent eq ker 28afad4fe744
-- statement:
--   The P2 M Ground Theory Heights  Heights cone Tangent eq ker 28afad4fe744 construction uses the P2 M Ground Theory Heights  Heights cone Tangent eq ker 28afad4fe744 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L38-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeJacMeasurable.lean#L38-L63

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

theorem P2M_GroundTheory_Heights__Heights_coneTangent_eq_ker_28afad4fe744 (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ}
    (g : Fin k → MvPolynomial (Fin n) ℂ) (hg : Submodule.span _ (Set.range g) = J)
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    coneTangent h J y = LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«coneTangent_eq_ker» := P2M_GroundTheory_Heights__Heights_coneTangent_eq_ker_28afad4fe744
