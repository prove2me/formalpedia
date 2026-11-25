-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_pairNum_fieldNum_8fffb03bfa94
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_pairNum_fieldNum_8fffb03bfa94
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:39:50.474147+00:00
-- url     : https://prove2.me/theorems/1d40d40b-2c04-5d39-bce4-ee06e307f855
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left pair Num field Num 8fffb03bfa94: P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left pair Num field Num 8fffb03b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left pair Num field Num 8fffb03bfa94 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Number Join Left pair Num field Num 8fffb03bfa94 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinPairNumJoinLeft.lean#L33-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinPairNumJoinLeft.lean#L33-L72

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_pairNum_fieldNum_8fffb03bfa94 {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ)
    (hP : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d) (I : IFamily (IsLocalRing.ResidueField O) ι)
    (hI : IsFieldIntersection I) {r : ℕ} (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O)
    (hv : ∀ l, IsVertDiv O P (y l - y' l) (f l) (g l)) (G : MvPolynomial (Fin r) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I P d y y' f g G =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) P d
        y y' f g G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairNumberJoinLeft».«pairNum_fieldNum» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberJoinLeft_pairNum_fieldNum_8fffb03bfa94
