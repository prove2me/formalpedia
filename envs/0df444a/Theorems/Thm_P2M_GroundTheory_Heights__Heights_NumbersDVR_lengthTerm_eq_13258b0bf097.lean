-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lengthTerm_eq_13258b0bf097
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_lengthTerm_eq_13258b0bf097
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:06.754826+00:00
-- url     : https://prove2.me/theorems/73477441-76b3-5a7d-9f4d-6c43719caa81
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length Term eq 13258b0bf097: P2 M Ground Theory Heights  Heights Numbers DVR length Term eq 13258b0bf097
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length Term eq 13258b0bf097 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length Term eq 13258b0bf097 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/OrdModEqLengthQuotSup.lean#L36-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/OrdModEqLengthQuotSup.lean#L36-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
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
open Module IsLocalRing ReciprocityTheory.ChartRestriction.G.AI
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_lengthTerm_eq_13258b0bf097 (hdim : ringKrullDim A = 1) (M : Type v) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (x : A) (p : PrimeSpectrum A) :
    (∑ᶠ (_ : ringKrullDim (A ⧸ p.asIdeal) = 1),
        length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
          ordMod p x) =
      ∑ᶠ (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes ∧
          p.asIdeal ≠ maximalIdeal A),
        length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
          length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x})) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«lengthTerm_eq» := P2M_GroundTheory_Heights__Heights_NumbersDVR_lengthTerm_eq_13258b0bf097
