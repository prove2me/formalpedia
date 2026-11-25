-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_comap_isMultiProjPrime_22590add1683
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_comap_isMultiProjPrime_22590add1683
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:08:07.223055+00:00
-- url     : https://prove2.me/theorems/a03fc589-3f34-40d8-baba-37ee3c7b52ba
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor comap is Multi Proj Prime 22590add1683: P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor comap is
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor comap is Multi Proj Prime 22590add1683 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Point Vertical Divisor comap is Multi Proj Prime 22590add1683 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointVertDiv.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinPointVertDiv.lean#L56-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointVertDiv
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord liftVar pullDeg joinCoord mcIdeal IsVertDiv)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinPointVerticalDivisor
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_comap_isMultiProjPrime_22590add1683 {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (liftVar (ι := ι) ι'))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinPointVerticalDivisor».«comap_isMultiProjPrime» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointVerticalDivisor_comap_isMultiProjPrime_22590add1683
