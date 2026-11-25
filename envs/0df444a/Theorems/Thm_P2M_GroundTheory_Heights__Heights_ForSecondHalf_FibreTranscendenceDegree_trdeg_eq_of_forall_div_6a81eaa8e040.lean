-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_eq_of_forall_div_6a81eaa8e040
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_eq_of_forall_div_6a81eaa8e040
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:55.768707+00:00
-- url     : https://prove2.me/theorems/d034fc77-c9e4-501c-8500-f43f855ec40d
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg eq of forall div 6a81eaa8e040: P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg eq of forall div 6a81eaa8e040 construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg eq of forall div 6a81eaa8e040 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L29-L39

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

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_eq_of_forall_div_6a81eaa8e040 {M : Type} [Field M] (B : Subalgebra ℤ M)
    (hZ : Function.Injective (algebraMap ℤ M))
    (h : ∀ m : M, ∃ a b : M, a ∈ B ∧ b ∈ B ∧ b ≠ 0 ∧ m = a / b) :
    Algebra.trdeg ℤ M = Algebra.trdeg ℤ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreTranscendenceDegree».«trdeg_eq_of_forall_div» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_eq_of_forall_div_6a81eaa8e040
