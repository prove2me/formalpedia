-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_quot_ker_49a962a5ab3c
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_quot_ker_49a962a5ab3c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:41:40.159028+00:00
-- url     : https://prove2.me/theorems/c265d6d8-e6bd-467a-b517-0784c061b2b7
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg quot ker 49a962a5ab3c: P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg quot ke
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg quot ker 49a962a5ab3c construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree trdeg quot ker 49a962a5ab3c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L41-L49

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

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_quot_ker_49a962a5ab3c {σ : Type} {M : Type} [CommRing M] [IsDomain M] (y : σ → M) :
    Algebra.trdeg ℤ (MvPolynomial σ ℤ ⧸ RingHom.ker (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M)) =
      Algebra.trdeg ℤ (aeval y : MvPolynomial σ ℤ →ₐ[ℤ] M).range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreTranscendenceDegree».«trdeg_quot_ker» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_quot_ker_49a962a5ab3c
