-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_subscheme__comp_eq_of_affineBlowup_lifts_fac79384cd03
-- name    : P2M_FunctorialResolution_EmbeddedResolution_subscheme__comp_eq_of_affineBlowup_lifts_fac79384cd03
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:33.303968+00:00
-- url     : https://prove2.me/theorems/9fb49b90-8009-40ea-91ae-f0f3d8205f2d
-- title:
--   P2 M Functorial Resolution Embedded Resolution subscheme  comp eq of affine Blowup lifts fac79384cd03: P2 M Functorial Resolution Embedded Resolution subscheme  comp eq of affine Blowup lifts fac79384
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution subscheme  comp eq of affine Blowup lifts fac79384cd03 construction uses the P2 M Functorial Resolution Embedded Resolution subscheme  comp eq of affine Blowup lifts fac79384cd03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L587-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/OrderReduction/BlowupChartCongruence.lean#L587-L619

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupCartier
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupChartPreimages
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_BlowupChartCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u
variable {R : Type u} [CommRing R]

theorem P2M_FunctorialResolution_EmbeddedResolution_subscheme__comp_eq_of_affineBlowup_lifts_fac79384cd03 (I : Ideal R) {W : Scheme.{u}}
    (ρ ρ' : W ⟶ Spec (CommRingCat.of R)) (𝔞 𝔟₁ : W.IdealSheafData)
    (h h' : W ⟶ Blowup.affineBlowup I)
    (hagree : 𝔞.subschemeι ≫ ρ = 𝔞.subschemeι ≫ ρ')
    (hpull : (Blowup.specIdealSheaf I).comap ρ = (Blowup.specIdealSheaf I).comap ρ')
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor ((Blowup.specIdealSheaf I).comap ρ))
    (hfac : (Blowup.specIdealSheaf I).comap ρ * 𝔟₁ = 𝔞)
    (hh : h ≫ Blowup.AffineBlowup.toSpec I = ρ)
    (hh' : h' ≫ Blowup.AffineBlowup.toSpec I = ρ') :
    𝔟₁.subschemeι ≫ h = 𝔟₁.subschemeι ≫ h' := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«subschemeι_comp_eq_of_affineBlowup_lifts» := P2M_FunctorialResolution_EmbeddedResolution_subscheme__comp_eq_of_affineBlowup_lifts_fac79384cd03
