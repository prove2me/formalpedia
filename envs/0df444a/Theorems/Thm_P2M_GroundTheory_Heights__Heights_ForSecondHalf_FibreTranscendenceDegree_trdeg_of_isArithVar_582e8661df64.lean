-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_of_isArithVar_582e8661df64
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_of_isArithVar_582e8661df64
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:18.467851+00:00
-- url     : https://prove2.me/theorems/60325415-9d8e-4691-b986-5bc3cfba4d0a
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg of is Arith Var 582e8661df64: P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg of is Arith Var 582e8661df64 construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg of is Arith Var 582e8661df64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L51-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L51-L66

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

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_of_isArithVar_582e8661df64 {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Ideal (MRing ι)}
    {n : ℕ} (h : IsArithVar J n) :
    ∃ t : ℕ, Algebra.trdeg ℤ (MRing ι ⧸ J) = t ∧ t + 1 = n + Fintype.card K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreTranscendenceDegree».«trdeg_of_isArithVar» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_of_isArithVar_582e8661df64
