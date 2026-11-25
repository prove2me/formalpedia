-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_dvd_primeProd_4e2ae87d1026
-- name    : P2M_GroundTheory_Heights__Heights_Model_dvd_primeProd_4e2ae87d1026
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:19.423765+00:00
-- url     : https://prove2.me/theorems/38815068-bfb5-4be5-b746-341d835cfa88
-- title:
--   P2 M Ground Theory Heights  Heights Model dvd prime Prod 4e2ae87d1026: P2 M Ground Theory Heights  Heights Model dvd prime Prod 4e2ae87d1026
-- statement:
--   The P2 M Ground Theory Heights  Heights Model dvd prime Prod 4e2ae87d1026 construction uses the P2 M Ground Theory Heights  Heights Model dvd prime Prod 4e2ae87d1026 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L52-L53

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

theorem P2M_GroundTheory_Heights__Heights_Model_dvd_primeProd_4e2ae87d1026 {p : Nat.Primes} (hp : p ∈ S) : ((p : ℕ) : ℤ) ∣ primeProd S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«dvd_primeProd» := P2M_GroundTheory_Heights__Heights_Model_dvd_primeProd_4e2ae87d1026
