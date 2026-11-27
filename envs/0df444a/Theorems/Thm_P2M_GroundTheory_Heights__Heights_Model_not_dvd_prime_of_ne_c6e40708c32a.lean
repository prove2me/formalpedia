-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_not_dvd_prime_of_ne_c6e40708c32a
-- name    : P2M_GroundTheory_Heights__Heights_Model_not_dvd_prime_of_ne_c6e40708c32a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:24.719362+00:00
-- url     : https://prove2.me/theorems/3a76dd42-8b8d-5127-a7d6-cdcec45195dd
-- title:
--   P2 M Ground Theory Heights  Heights Model not dvd prime of ne c6e40708c32a: P2 M Ground Theory Heights  Heights Model not dvd prime of ne c6e40708c32a
-- statement:
--   The P2 M Ground Theory Heights  Heights Model not dvd prime of ne c6e40708c32a construction uses the P2 M Ground Theory Heights  Heights Model not dvd prime of ne c6e40708c32a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L65-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueSat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type} [Field Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]

theorem P2M_GroundTheory_Heights__Heights_Model_not_dvd_prime_of_ne_c6e40708c32a {p q : Nat.Primes} (h : q ≠ p) : ¬ ((p : ℕ) : ℤ) ∣ ((q : ℕ) : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«not_dvd_prime_of_ne» := P2M_GroundTheory_Heights__Heights_Model_not_dvd_prime_of_ne_c6e40708c32a
