-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_prime_mem_chartRing_6e030817a089
-- name    : P2M_GroundTheory_Heights__Heights_Model_inv_prime_mem_chartRing_6e030817a089
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:12.68439+00:00
-- url     : https://prove2.me/theorems/7acfe905-4245-419e-827d-18fce5ea42b0
-- title:
--   P2 M Ground Theory Heights  Heights Model inv prime mem chart Ring 6e030817a089: P2 M Ground Theory Heights  Heights Model inv prime mem chart Ring 6e030817a089
-- statement:
--   The P2 M Ground Theory Heights  Heights Model inv prime mem chart Ring 6e030817a089 construction uses the P2 M Ground Theory Heights  Heights Model inv prime mem chart Ring 6e030817a089 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L72-L82

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
variable (x o₀)

theorem P2M_GroundTheory_Heights__Heights_Model_inv_prime_mem_chartRing_6e030817a089 {p : Nat.Primes} (hp : p ∈ S) (i : τ) :
    (((p : ℕ) : ℤ) : Ω)⁻¹ ∈ chartRing o₀ x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«inv_prime_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Model_inv_prime_mem_chartRing_6e030817a089
