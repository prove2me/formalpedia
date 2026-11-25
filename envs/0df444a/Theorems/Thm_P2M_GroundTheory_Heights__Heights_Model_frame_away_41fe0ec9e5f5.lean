-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_frame_away_41fe0ec9e5f5
-- name    : P2M_GroundTheory_Heights__Heights_Model_frame_away_41fe0ec9e5f5
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:19.166954+00:00
-- url     : https://prove2.me/theorems/41398233-4b34-48a0-b083-d3d1e1c57eba
-- title:
--   P2 M Ground Theory Heights  Heights Model frame away 41fe0ec9e5f5: P2 M Ground Theory Heights  Heights Model frame away 41fe0ec9e5f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Model frame away 41fe0ec9e5f5 construction uses the P2 M Ground Theory Heights  Heights Model frame away 41fe0ec9e5f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L76-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/ChartGlueFrame.lean#L76-L126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrame
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
  {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}

theorem P2M_GroundTheory_Heights__Heights_Model_frame_away_41fe0ec9e5f5 {i : τ} (hi : x i ≠ 0)
    (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) (Q : Ideal (chartRing ℤ x i))
    (hQ : Q.IsPrime) (hmQ : ((primeProd S : ℤ) : chartRing ℤ x i) ∉ Q) :
    ∃ h : Ω, ∃ hh : h ∈ chartRing ℤ x i, (⟨h, hh⟩ : chartRing ℤ x i) ∉ Q ∧
      IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«frame_away» := P2M_GroundTheory_Heights__Heights_Model_frame_away_41fe0ec9e5f5
