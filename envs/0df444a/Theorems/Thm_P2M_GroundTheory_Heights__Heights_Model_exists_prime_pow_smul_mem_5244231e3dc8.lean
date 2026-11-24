-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_prime_pow_smul_mem_5244231e3dc8
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_prime_pow_smul_mem_5244231e3dc8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:25.398498+00:00
-- url     : https://prove2.me/theorems/3c91ce08-ecf0-472a-bf36-81fc9b24aa5e
-- title:
--   P2 M Ground Theory Heights  Heights Model exists prime pow smul mem 5244231e3dc8: P2 M Ground Theory Heights  Heights Model exists prime pow smul mem 5244231e3dc8
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists prime pow smul mem 5244231e3dc8 construction uses the P2 M Ground Theory Heights  Heights Model exists prime pow smul mem 5244231e3dc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L102-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L102-L117

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
variable (B₀ : ChartBundle o₀ x r E) (Bp : ∀ p, ChartBundle (o p) x r E)
variable {B₀ Bp}

theorem P2M_GroundTheory_Heights__Heights_Model_exists_prime_pow_smul_mem_5244231e3dc8 {i : τ} (p : S)
    (hSR : SameRationalSpan (B₀.lat i) ((Bp p).lat i)) {w : E} (hw : w ∈ B₀.lat i) :
    ∃ k : ℕ, ((((p : Nat.Primes) : ℕ) : ℤ) : Ω) ^ k • w ∈ (Bp p).lat i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_prime_pow_smul_mem» := P2M_GroundTheory_Heights__Heights_Model_exists_prime_pow_smul_mem_5244231e3dc8
