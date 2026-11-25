-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_eq_add_ffdf45e96f09
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_eq_add_ffdf45e96f09
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:01.680979+00:00
-- url     : https://prove2.me/theorems/1ca197cc-3ed0-4443-a957-a417bdea5bbc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized eq add ffdf45e96f09: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samue
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized eq add ffdf45e96f09 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Hilbert Samuel length localized eq add ffdf45e96f09 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LengthLocalizedQuotientEqZero.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/LengthLocalizedQuotientEqZero.lean#L37-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_eq_add_ffdf45e96f09 (p : Ideal R) [p.IsPrime] {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) (hf : Function.Injective f)
    (hg : Function.Surjective g) (h : Function.Exact f g) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₁) =
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₀) +
      Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M₂) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«HilbertSamuel».«length_localized_eq_add» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_eq_add_ffdf45e96f09
