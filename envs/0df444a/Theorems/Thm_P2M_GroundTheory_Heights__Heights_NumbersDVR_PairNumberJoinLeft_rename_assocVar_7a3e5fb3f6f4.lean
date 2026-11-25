-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_rename_assocVar_7a3e5fb3f6f4
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_rename_assocVar_7a3e5fb3f6f4
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:13.638234+00:00
-- url     : https://prove2.me/theorems/deb29544-42fd-5a80-bee7-28a8af3febf2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left rename assoc Var 7a3e5fb3f6f4: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left rename assoc Var 7a3e5fb3f6f4
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left rename assoc Var 7a3e5fb3f6f4 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left rename assoc Var 7a3e5fb3f6f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinPairNumJoinLeft.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinPairNumJoinLeft.lean#L128-L133

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_rename_assocVar_7a3e5fb3f6f4 {R : Type} [CommRing R] (f : MRing (Sum.elim ι ι') R) :
    rename (assocVar ι₂) f = rename (assocSigma ι ι' ι₂) (joinForm (ι' := ι₂) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberJoinLeft».«rename_assocVar» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_rename_assocVar_7a3e5fb3f6f4
