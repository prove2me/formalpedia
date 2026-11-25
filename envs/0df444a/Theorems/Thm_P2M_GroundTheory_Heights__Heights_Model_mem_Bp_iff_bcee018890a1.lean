-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_mem_Bp_iff_bcee018890a1
-- name    : P2M_GroundTheory_Heights__Heights_Model_mem_Bp_iff_bcee018890a1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:46.753801+00:00
-- url     : https://prove2.me/theorems/2219efe1-1ff1-40bc-8411-cfe90096e6bf
-- title:
--   P2 M Ground Theory Heights  Heights Model mem Bp iff bcee018890a1: P2 M Ground Theory Heights  Heights Model mem Bp iff bcee018890a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Model mem Bp iff bcee018890a1 construction uses the P2 M Ground Theory Heights  Heights Model mem Bp iff bcee018890a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L158-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L158-L203

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

theorem P2M_GroundTheory_Heights__Heights_Model_mem_Bp_iff_bcee018890a1 [CharZero Ω] {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (p : S) (v : E) :
    v ∈ (Bp p).lat i ↔ ∃ s : ℤ, ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ s ∧ s • v ∈ glueLat B₀ Bp i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«mem_Bp_iff» := P2M_GroundTheory_Heights__Heights_Model_mem_Bp_iff_bcee018890a1
