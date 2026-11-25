-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ringKrullDim_imageVar_fd8895e43c69
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ringKrullDim_imageVar_fd8895e43c69
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:06:12.804616+00:00
-- url     : https://prove2.me/theorems/ce22a61a-7dcd-4bbd-be25-1c68cda404c2
-- title:
--   P2 M Ground Theory Heights  Heights Targets Proj Contract ring Krull Dim image Var fd8895e43c69: P2 M Ground Theory Heights  Heights Targets Proj Contract ring Krull Dim image Var fd8895e43c69
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Proj Contract ring Krull Dim image Var fd8895e43c69 construction uses the P2 M Ground Theory Heights  Heights Targets Proj Contract ring Krull Dim image Var fd8895e43c69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean#L103-L111

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ringKrullDim_imageVar_fd8895e43c69 (hv : AI.I1.IsBlockMap κ v) (V' : Ideal (Geo.MRingOver F ι')) :
    ringKrullDim (Geo.MRingOver F ι ⧸ AI.I1.imageVar F v V') =
      ringKrullDim (NumbersDVR.MRing (fun k => ι' (emb hv k)) F ⧸
        FieldNumbers.contractPrime (emb hv) V') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ProjContract».«ringKrullDim_imageVar» := P2M_GroundTheory_Heights__Heights_Targets_ProjContract_ringKrullDim_imageVar_fd8895e43c69
