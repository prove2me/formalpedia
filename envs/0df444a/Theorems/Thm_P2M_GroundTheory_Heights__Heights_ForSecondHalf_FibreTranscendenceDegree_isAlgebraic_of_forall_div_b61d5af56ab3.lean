-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_isAlgebraic_of_forall_div_b61d5af56ab3
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_isAlgebraic_of_forall_div_b61d5af56ab3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:17.504147+00:00
-- url     : https://prove2.me/theorems/12e843ed-e8da-4626-a09d-4aa3c53098e3
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree is Algebraic of forall div b61d5af56ab3: P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree i
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree is Algebraic of forall div b61d5af56ab3 construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree is Algebraic of forall div b61d5af56ab3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L16-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFibreMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_isAlgebraic_of_forall_div_b61d5af56ab3 {M : Type} [Field M] (B : Subalgebra ℤ M)
    (h : ∀ m : M, ∃ a b : M, a ∈ B ∧ b ∈ B ∧ b ≠ 0 ∧ m = a / b) : Algebra.IsAlgebraic B M := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreTranscendenceDegree».«isAlgebraic_of_forall_div» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_isAlgebraic_of_forall_div_b61d5af56ab3
