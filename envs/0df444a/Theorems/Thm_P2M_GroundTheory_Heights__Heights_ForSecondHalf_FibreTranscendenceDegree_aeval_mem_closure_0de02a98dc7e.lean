-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_aeval_mem_closure_0de02a98dc7e
-- name    : P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_aeval_mem_closure_0de02a98dc7e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:20:20.753327+00:00
-- url     : https://prove2.me/theorems/dc2e60af-abd1-4d89-ba29-dba0e73193c1
-- title:
--   P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree aeval mem closure 0de02a98dc7e: P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree aeval mem
-- statement:
--   The P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree aeval mem closure 0de02a98dc7e construction uses the P2 M Ground Theory Heights  Heights For Second Half Fibre Transcendence Degree aeval mem closure 0de02a98dc7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/SemipositiveHeights/FibreDim.lean#L68-L73

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

theorem P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_aeval_mem_closure_0de02a98dc7e {σ : Type} {L : Type} [Field L] (y : σ → L) (f : MvPolynomial σ ℤ) :
    aeval y f ∈ Subfield.closure (Set.range y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ForSecondHalf».«FibreTranscendenceDegree».«aeval_mem_closure» := P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_aeval_mem_closure_0de02a98dc7e
