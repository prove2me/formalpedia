-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finrank_coneTangent_of_jacobian_0027e1f387a0
-- name    : P2M_GroundTheory_Heights__Heights_finrank_coneTangent_of_jacobian_0027e1f387a0
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:47:05.764733+00:00
-- url     : https://prove2.me/theorems/1fac6417-4c9d-4011-8604-d0dd7900afc0
-- title:
--   P2 M Ground Theory Heights  Heights finrank cone Tangent of jacobian 0027e1f387a0: P2 M Ground Theory Heights  Heights finrank cone Tangent of jacobian 0027e1f387a0
-- statement:
--   The P2 M Ground Theory Heights  Heights finrank cone Tangent of jacobian 0027e1f387a0 construction uses the P2 M Ground Theory Heights  Heights finrank cone Tangent of jacobian 0027e1f387a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L40-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeTangentDim.lean#L40-L101

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

theorem P2M_GroundTheory_Heights__Heights_finrank_coneTangent_of_jacobian_0027e1f387a0 (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ)
    (hf : ∀ k, f k ∈ J) (hs : ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f))
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ coneSet h J) (hsy : eval (h.pointOf y) s ≠ 0)
    (hD : eval (h.pointOf y) (frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f) ≠ 0) :
    finrank ℂ (coneTangent h J y) = I₀.card := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finrank_coneTangent_of_jacobian» := P2M_GroundTheory_Heights__Heights_finrank_coneTangent_of_jacobian_0027e1f387a0
