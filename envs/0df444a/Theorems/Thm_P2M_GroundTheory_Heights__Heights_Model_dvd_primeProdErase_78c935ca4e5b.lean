-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_dvd_primeProdErase_78c935ca4e5b
-- name    : P2M_GroundTheory_Heights__Heights_Model_dvd_primeProdErase_78c935ca4e5b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:27.759805+00:00
-- url     : https://prove2.me/theorems/f75b9f12-c737-4472-8f8e-a6fea7dcb2d5
-- title:
--   P2 M Ground Theory Heights  Heights Model dvd prime Prod Erase 78c935ca4e5b: P2 M Ground Theory Heights  Heights Model dvd prime Prod Erase 78c935ca4e5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Model dvd prime Prod Erase 78c935ca4e5b construction uses the P2 M Ground Theory Heights  Heights Model dvd prime Prod Erase 78c935ca4e5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L55-L57

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

theorem P2M_GroundTheory_Heights__Heights_Model_dvd_primeProdErase_78c935ca4e5b {p q : Nat.Primes} (hq : q ∈ S) (hqp : q ≠ p) :
    ((q : ℕ) : ℤ) ∣ primeProdErase S p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«dvd_primeProdErase» := P2M_GroundTheory_Heights__Heights_Model_dvd_primeProdErase_78c935ca4e5b
