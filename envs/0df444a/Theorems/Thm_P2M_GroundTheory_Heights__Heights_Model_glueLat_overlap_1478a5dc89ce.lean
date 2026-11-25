-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glueLat_overlap_1478a5dc89ce
-- name    : P2M_GroundTheory_Heights__Heights_Model_glueLat_overlap_1478a5dc89ce
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:44:23.806127+00:00
-- url     : https://prove2.me/theorems/ac9b1394-09fa-5da9-938c-7b029bcc88f3
-- title:
--   P2 M Ground Theory Heights  Heights Model glue Lat overlap 1478a5dc89ce: P2 M Ground Theory Heights  Heights Model glue Lat overlap 1478a5dc89ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Model glue Lat overlap 1478a5dc89ce construction uses the P2 M Ground Theory Heights  Heights Model glue Lat overlap 1478a5dc89ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L211-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L211-L223

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

theorem P2M_GroundTheory_Heights__Heights_Model_glueLat_overlap_1478a5dc89ce (i j : τ) (hi : x i ≠ 0) (hj : x j ≠ 0) (e : E)
    (he : e ∈ glueLat B₀ Bp i) : ∃ m : ℕ, (x i / x j) ^ m • e ∈ glueLat B₀ Bp j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«glueLat_overlap» := P2M_GroundTheory_Heights__Heights_Model_glueLat_overlap_1478a5dc89ce
