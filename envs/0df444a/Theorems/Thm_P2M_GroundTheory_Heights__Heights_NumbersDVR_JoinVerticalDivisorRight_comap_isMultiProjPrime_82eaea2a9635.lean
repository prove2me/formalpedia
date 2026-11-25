-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_comap_isMultiProjPrime_82eaea2a9635
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_comap_isMultiProjPrime_82eaea2a9635
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:08:52.907522+00:00
-- url     : https://prove2.me/theorems/85fe9b4e-a8bd-4a50-83c2-2d0127bec401
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right comap is Multi Proj Prime 82eaea2a9635: P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right comap is
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right comap is Multi Proj Prime 82eaea2a9635 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Vertical Divisor Right comap is Multi Proj Prime 82eaea2a9635 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L108-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinJoinVertDivRight.lean#L108-L123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinVertDivRight
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisorRight
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}
variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_comap_isMultiProjPrime_82eaea2a9635 {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinVerticalDivisorRight».«comap_isMultiProjPrime» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinVerticalDivisorRight_comap_isMultiProjPrime_82eaea2a9635
