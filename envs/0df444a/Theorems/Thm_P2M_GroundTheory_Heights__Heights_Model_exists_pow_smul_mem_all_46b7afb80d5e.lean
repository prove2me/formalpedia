-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_all_46b7afb80d5e
-- name    : P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_all_46b7afb80d5e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:17.911709+00:00
-- url     : https://prove2.me/theorems/5bc5ade7-0bb8-42e4-8628-b78c6e9e60fa
-- title:
--   P2 M Ground Theory Heights  Heights Model exists pow smul mem all 46b7afb80d5e: P2 M Ground Theory Heights  Heights Model exists pow smul mem all 46b7afb80d5e
-- statement:
--   The P2 M Ground Theory Heights  Heights Model exists pow smul mem all 46b7afb80d5e construction uses the P2 M Ground Theory Heights  Heights Model exists pow smul mem all 46b7afb80d5e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L119-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueLat.lean#L119-L136

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

theorem P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_all_46b7afb80d5e {i : τ} (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i))
    {w : E} (hw : w ∈ B₀.lat i) (z : ℤ) (P : S → Prop)
    (hz : ∀ p, P p → (((p : Nat.Primes) : ℕ) : ℤ) ∣ z) :
    ∃ K : ℕ, ∀ K' ≥ K, ∀ p, P p → ((z : Ω) ^ K') • w ∈ (Bp p).lat i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«exists_pow_smul_mem_all» := P2M_GroundTheory_Heights__Heights_Model_exists_pow_smul_mem_all_46b7afb80d5e
