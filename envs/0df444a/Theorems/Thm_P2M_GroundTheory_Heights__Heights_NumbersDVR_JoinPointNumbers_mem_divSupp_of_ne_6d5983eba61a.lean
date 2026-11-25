-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointNumbers_mem_divSupp_of_ne_6d5983eba61a
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointNumbers_mem_divSupp_of_ne_6d5983eba61a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:29:31.819133+00:00
-- url     : https://prove2.me/theorems/60d5074f-f380-4341-83e0-a9473ee501ad
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Numbers mem div Supp of ne 6d5983eba61a: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Numbers mem div Supp of ne 6d5983eba61a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Numbers mem div Supp of ne 6d5983eba61a construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Numbers mem div Supp of ne 6d5983eba61a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointNumbers.lean#L98-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointNumbers.lean#L98-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinPointIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinVariety
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalComponentFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointNumbers
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointNumbers
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointNumbers_mem_divSupp_of_ne_6d5983eba61a {R : Type} [CommRing R] [IsNoetherianRing R] (P : Ideal (MRing ι R))
    (s : MRing ι R) (W : Ideal (MRing ι R)) (h : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W ≠ 0) :
    W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointNumbers».«mem_divSupp_of_ne» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointNumbers_mem_divSupp_of_ne_6d5983eba61a
