-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_frame_at_prime_1f139d9a93c6
-- name    : P2M_GroundTheory_Heights__Heights_Model_frame_at_prime_1f139d9a93c6
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:56.737788+00:00
-- url     : https://prove2.me/theorems/1fde7c69-7f07-4d6a-a1c9-d6a9cbfbb579
-- title:
--   P2 M Ground Theory Heights  Heights Model frame at prime 1f139d9a93c6: P2 M Ground Theory Heights  Heights Model frame at prime 1f139d9a93c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Model frame at prime 1f139d9a93c6 construction uses the P2 M Ground Theory Heights  Heights Model frame at prime 1f139d9a93c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrameP.lean#L26-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrameP.lean#L26-L198

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrameP
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
variable {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
  {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
  {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
  {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
  [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
  [∀ p, Algebra (o p) Ω]
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}

theorem P2M_GroundTheory_Heights__Heights_Model_frame_at_prime_1f139d9a93c6 {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (p : S) (hpQ : ((((p : Nat.Primes) : ℕ) : ℤ) : (chartRing ℤ x i)) ∈ Q) :
    ∃ h : Ω, ∃ hh : h ∈ (chartRing ℤ x i), (⟨h, hh⟩ : (chartRing ℤ x i)) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«frame_at_prime» := P2M_GroundTheory_Heights__Heights_Model_frame_at_prime_1f139d9a93c6
