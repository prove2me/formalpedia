-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_homogeneousComponent_mul_of_isHomogeneous_right_3ca43a8912fb
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_homogeneousComponent_mul_of_isHomogeneous_right_3ca43a8912fb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:16.242175+00:00
-- url     : https://prove2.me/theorems/a0e9d38f-5f12-4fe6-b7b4-512b87631df4
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets homogeneous Component mul of is Homogeneous right 3ca43a8912fb: P2 M Ground Theory Heights  Heights Complex Sets homogeneous Component mul of is Homoge
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets homogeneous Component mul of is Homogeneous right 3ca43a8912fb construction uses the P2 M Ground Theory Heights  Heights Complex Sets homogeneous Component mul of is Homogeneous right 3ca43a8912fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsFinite.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PConeAvoidsFinite.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_homogeneousComponent_mul_of_isHomogeneous_right_3ca43a8912fb {σ : Type*} (a g : MvPolynomial σ ℂ)
    {e : ℕ} (hg : g.IsHomogeneous e) (k : ℕ) :
    homogeneousComponent k (a * g) = if e ≤ k then homogeneousComponent (k - e) a * g else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«homogeneousComponent_mul_of_isHomogeneous_right» := P2M_GroundTheory_Heights__Heights_ComplexSets_homogeneousComponent_mul_of_isHomogeneous_right_3ca43a8912fb
