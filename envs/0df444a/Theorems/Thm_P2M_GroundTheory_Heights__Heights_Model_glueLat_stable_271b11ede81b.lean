-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glueLat_stable_271b11ede81b
-- name    : P2M_GroundTheory_Heights__Heights_Model_glueLat_stable_271b11ede81b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:13.438066+00:00
-- url     : https://prove2.me/theorems/a6f2b9ba-019e-48eb-bf61-1ab16d842970
-- title:
--   P2 M Ground Theory Heights  Heights Model glue Lat stable 271b11ede81b: P2 M Ground Theory Heights  Heights Model glue Lat stable 271b11ede81b
-- statement:
--   The P2 M Ground Theory Heights  Heights Model glue Lat stable 271b11ede81b construction uses the P2 M Ground Theory Heights  Heights Model glue Lat stable 271b11ede81b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L205-L209

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

theorem P2M_GroundTheory_Heights__Heights_Model_glueLat_stable_271b11ede81b (i : τ) (a : Ω) (ha : a ∈ chartRing ℤ x i) (e : E)
    (he : e ∈ glueLat B₀ Bp i) : a • e ∈ glueLat B₀ Bp i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«glueLat_stable» := P2M_GroundTheory_Heights__Heights_Model_glueLat_stable_271b11ede81b
