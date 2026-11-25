-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_assocSigma_symm_fst_ff1bf713bfa5
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_assocSigma_symm_fst_ff1bf713bfa5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:40.951998+00:00
-- url     : https://prove2.me/theorems/e4cb9574-15ef-5bf6-816f-d1e3588fb3a3
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left assoc Sigma symm fst ff1bf713bfa5: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left assoc Sigma symm fst ff1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left assoc Sigma symm fst ff1bf713bfa5 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left assoc Sigma symm fst ff1bf713bfa5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinPairNumJoinLeft.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinPairNumJoinLeft.lean#L94-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InhabitLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinDivDiffExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointNumbers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalComponentFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFibreVarieties
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericDimGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PComponentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinPairNumJoinLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection IsProjVarF)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord fnField assocDeg assocVar)
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberJoinLeft
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_assocSigma_symm_fst_ff1bf713bfa5 (v : Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) :
    ((assocSigma ι ι' ι₂).symm v).1 = (Equiv.sumAssoc K K' K₂).symm v.1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberJoinLeft».«assocSigma_symm_fst» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_assocSigma_symm_fst_ff1bf713bfa5
