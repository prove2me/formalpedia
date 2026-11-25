-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_mul_mem_of_algebraMap_mem_ad35f2d7d286
-- name    : P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_mul_mem_of_algebraMap_mem_ad35f2d7d286
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:36.012496+00:00
-- url     : https://prove2.me/theorems/dec52a84-32e4-4283-b441-5bf6a5b9687d
-- title:
--   P2 M Ground Theory Heights  Heights Jacobian At Curve Point exists mul mem of algebra Map mem ad35f2d7d286: P2 M Ground Theory Heights  Heights Jacobian At Curve Point exists mul mem of algebra Map me
-- statement:
--   The P2 M Ground Theory Heights  Heights Jacobian At Curve Point exists mul mem of algebra Map mem ad35f2d7d286 construction uses the P2 M Ground Theory Heights  Heights Jacobian At Curve Point exists mul mem of algebra Map mem ad35f2d7d286 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/JacobianAtCurvePoint.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/JacobianAtCurvePoint.lean#L26-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_JacobianAtCurvePoint
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
open MvPolynomial IsLocalRing GradientAtPoint
noncomputable section
open GroundTheory.Heights₂.Heights.JacobianAtCurvePoint
variable {σ : Type}

theorem P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_mul_mem_of_algebraMap_mem_ad35f2d7d286 (w : σ → ℂ) (J : Ideal (MvPolynomial σ ℂ)) (x : MvPolynomial σ ℂ)
    (hx : algebraMap _ (ptLoc w) x ∈ J.map (algebraMap _ (ptLoc w))) :
    ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * x ∈ J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«JacobianAtCurvePoint».«exists_mul_mem_of_algebraMap_mem» := P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_mul_mem_of_algebraMap_mem_ad35f2d7d286
