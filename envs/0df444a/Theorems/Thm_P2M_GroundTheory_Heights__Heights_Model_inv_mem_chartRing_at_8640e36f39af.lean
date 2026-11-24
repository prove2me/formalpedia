-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_at_8640e36f39af
-- name    : P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_at_8640e36f39af
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:09.899189+00:00
-- url     : https://prove2.me/theorems/22efef30-876f-4bb7-8eb1-1ba87e18b3ef
-- title:
--   P2 M Ground Theory Heights  Heights Model inv mem chart Ring at 8640e36f39af: P2 M Ground Theory Heights  Heights Model inv mem chart Ring at 8640e36f39af
-- statement:
--   The P2 M Ground Theory Heights  Heights Model inv mem chart Ring at 8640e36f39af construction uses the P2 M Ground Theory Heights  Heights Model inv mem chart Ring at 8640e36f39af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L36-L38

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
variable (x)

theorem P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_at_8640e36f39af (p : S) (i : τ) {s : ℤ} (hs : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s) :
    (s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ chartRing (o p) x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«inv_mem_chartRing_at» := P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_at_8640e36f39af
