-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_minimalPrimes_map_equiv_83a5b4407833
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_minimalPrimes_map_equiv_83a5b4407833
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:34:13.600293+00:00
-- url     : https://prove2.me/theorems/12453177-615f-496a-bf81-c24b97178b80
-- title:
--   P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity minimal Primes map equiv 83a5b4407833: P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity minimal P
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity minimal Primes map equiv 83a5b4407833 construction uses the P2 M Ground Theory Heights  Heights Objects Chow Vertical Part Multiplicity minimal Primes map equiv 83a5b4407833 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LengthLocalizedModuleQuotient.lean#L131-L134

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LengthLocalizedModuleQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ObjectsChow
open GroundTheory.Heights₂.Heights.ObjectsChow.VerticalPartMultiplicity
open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_minimalPrimes_map_equiv_83a5b4407833 {A B : Type*} [CommRing A] [CommRing B] (Φ : A ≃+* B) (K : Ideal A) :
    (K.map (Φ : A →+* B)).minimalPrimes = Ideal.map (Φ : A →+* B) '' K.minimalPrimes := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsChow».«VerticalPartMultiplicity».«minimalPrimes_map_equiv» := P2M_GroundTheory_Heights__Heights_ObjectsChow_VerticalPartMultiplicity_minimalPrimes_map_equiv_83a5b4407833
