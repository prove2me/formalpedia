-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_inv_prod_mem_chartRing_6138e0eacf84
-- name    : P2M_GroundTheory_Heights__Heights_Model_inv_prod_mem_chartRing_6138e0eacf84
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:52.438705+00:00
-- url     : https://prove2.me/theorems/0ccb1817-9537-4122-a6e1-a87eb4b48406
-- title:
--   P2 M Ground Theory Heights  Heights Model inv prod mem chart Ring 6138e0eacf84: P2 M Ground Theory Heights  Heights Model inv prod mem chart Ring 6138e0eacf84
-- statement:
--   The P2 M Ground Theory Heights  Heights Model inv prod mem chart Ring 6138e0eacf84 construction uses the P2 M Ground Theory Heights  Heights Model inv prod mem chart Ring 6138e0eacf84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L42-L44

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

theorem P2M_GroundTheory_Heights__Heights_Model_inv_prod_mem_chartRing_6138e0eacf84 (i : τ) :
    ((primeProd S : ℤ) : Ω) ≠ 0 ∧ ((primeProd S : ℤ) : Ω)⁻¹ ∈ chartRing o₀ x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«inv_prod_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Model_inv_prod_mem_chartRing_6138e0eacf84
