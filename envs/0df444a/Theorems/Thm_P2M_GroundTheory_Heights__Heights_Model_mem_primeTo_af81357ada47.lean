-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_primeTo_af81357ada47
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_primeTo_af81357ada47
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:57.643202+00:00
-- url     : https://prove2.me/theorems/a87d6a6e-d6b8-438c-b113-ce23db421ede
-- title:
--   P2 M Ground Theory Heights  Heights Model mem prime To af81357ada47: P2 M Ground Theory Heights  Heights Model mem prime To af81357ada47
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem prime To af81357ada47 construction uses the P2 M Ground Theory Heights  Heights Model mem prime To af81357ada47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_Model_mem_primeTo_af81357ada47 {p : Nat.Primes} {s : ℤ} : s ∈ primeTo p ↔ ¬ ((p : ℕ) : ℤ) ∣ s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_primeTo» := P2M_GroundTheory_Heights__Heights_Model_mem_primeTo_af81357ada47
