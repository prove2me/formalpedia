-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_smul_mem_3c62fb0adb4f
-- name    : P2M_GroundTheory_Heights__Heights_Model_intCast_smul_mem_3c62fb0adb4f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:14.028858+00:00
-- url     : https://prove2.me/theorems/622f69b6-e368-48d4-866f-1b86ba20f7ea
-- title:
--   P2 M Ground Theory Heights  Heights Model int Cast smul mem 3c62fb0adb4f: P2 M Ground Theory Heights  Heights Model int Cast smul mem 3c62fb0adb4f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model int Cast smul mem 3c62fb0adb4f construction uses the P2 M Ground Theory Heights  Heights Model int Cast smul mem 3c62fb0adb4f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L88-L90

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

theorem P2M_GroundTheory_Heights__Heights_Model_intCast_smul_mem_3c62fb0adb4f {R : Type*} [CommRing R] [Algebra R Ω] (B : ChartBundle R x r E) {i : τ}
    (z : ℤ) {e : E} (he : e ∈ B.lat i) : (z : Ω) • e ∈ B.lat i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«intCast_smul_mem» := P2M_GroundTheory_Heights__Heights_Model_intCast_smul_mem_3c62fb0adb4f
