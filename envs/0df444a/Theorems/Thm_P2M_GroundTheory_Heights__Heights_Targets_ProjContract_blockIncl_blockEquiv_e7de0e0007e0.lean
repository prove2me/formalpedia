-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjContract_blockIncl_blockEquiv_e7de0e0007e0
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjContract_blockIncl_blockEquiv_e7de0e0007e0
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:08:52.066338+00:00
-- url     : https://prove2.me/theorems/7d1dfb8a-80d2-4665-b7dd-6d4253b92612
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Contract block Incl block Equiv e7de0e0007e0: P2 M Ground Theory Heights  Heights Targets Proj Contract block Incl block Equiv e7de0e0007e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Contract block Incl block Equiv e7de0e0007e0 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Contract block Incl block Equiv e7de0e0007e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L90-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjContract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Targets.ProjContract
variable {F : Type u} [Field F] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjContract_blockIncl_blockEquiv_e7de0e0007e0 (hv : AI.I1.IsBlockMap κ v) (p : Σ k, ι k) :
    FieldNumbers.blockIncl (emb hv) ι' (blockEquiv hv p) = v p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjContract».«blockIncl_blockEquiv» := P2M_GroundTheory_Heights__Heights_Targets_ProjContract_blockIncl_blockEquiv_e7de0e0007e0
