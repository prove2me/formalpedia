-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_mul_2dccd2fab054
-- name    : P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_mul_2dccd2fab054
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:58.329483+00:00
-- url     : https://prove2.me/theorems/71a2366d-40e4-455f-90a0-baac96a525b1
-- title:
--   P2 M Ground Theory Heights  Heights Model prime Prod eq mul 2dccd2fab054: P2 M Ground Theory Heights  Heights Model prime Prod eq mul 2dccd2fab054
-- statement:
--   The P2 M Ground Theory Heights  Heights Model prime Prod eq mul 2dccd2fab054 construction uses the P2 M Ground Theory Heights  Heights Model prime Prod eq mul 2dccd2fab054 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L48-L50

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

theorem P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_mul_2dccd2fab054 {p : Nat.Primes} (hp : p ∈ S) :
    primeProd S = ((p : ℕ) : ℤ) * primeProdErase S p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«primeProd_eq_mul» := P2M_GroundTheory_Heights__Heights_Model_primeProd_eq_mul_2dccd2fab054
