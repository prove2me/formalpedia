-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFilt_card_prime_eq_length_c94425c30737
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFilt_card_prime_eq_length_c94425c30737
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:29:17.745686+00:00
-- url     : https://prove2.me/theorems/86d13132-04f2-4dc0-8718-b7e619ba7f96
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Prime Filt card prime eq length c94425c30737: P2 M Ground Theory Heights  Heights Kleiman Prime Filt card prime eq length c94425c30737
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Prime Filt card prime eq length c94425c30737 construction uses the P2 M Ground Theory Heights  Heights Kleiman Prime Filt card prime eq length c94425c30737 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationExists.lean#L234-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PPrimeFiltrationExists.lean#L234-L317

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.PrimeFilt
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  {𝓜 : GradedPMod S N M}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFilt_card_prime_eq_length_c94425c30737 (F : PrimeFilt 𝓜) (pp : Ideal (Poly S N)) [pp.IsPrime]
    (hpp : pp ∈ (Module.annihilator (Poly S N) M).minimalPrimes) :
    (((Finset.univ.filter fun k => F.prime k = pp).card : ℕ) : ℕ∞) =
      Module.length (Localization.AtPrime pp) (LocalizedModule pp.primeCompl M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«PrimeFilt».«card_prime_eq_length» := P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFilt_card_prime_eq_length_c94425c30737
