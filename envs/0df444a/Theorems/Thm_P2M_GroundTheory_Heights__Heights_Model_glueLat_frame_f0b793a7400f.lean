-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_glueLat_frame_f0b793a7400f
-- name    : P2M_GroundTheory_Heights__Heights_Model_glueLat_frame_f0b793a7400f
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:03.325591+00:00
-- url     : https://prove2.me/theorems/2f9d5902-73a7-4b6b-a5d8-f2b8f890303d
-- title:
--   P2 M Ground Theory Heights  Heights Model glue Lat frame f0b793a7400f: P2 M Ground Theory Heights  Heights Model glue Lat frame f0b793a7400f
-- statement:
--   The P2 M Ground Theory Heights  Heights Model glue Lat frame f0b793a7400f construction uses the P2 M Ground Theory Heights  Heights Model glue Lat frame f0b793a7400f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PChartGlue.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PChartGlue.lean#L10-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueFrameP
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PChartGlue
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

theorem P2M_GroundTheory_Heights__Heights_Model_glueLat_frame_f0b793a7400f {Ω : Type} [Field Ω] [CharZero Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {S : Finset Nat.Primes}
    {o₀ : Type} [CommRing o₀] [Algebra ℤ o₀] [IsLocalization.Away (primeProd S) o₀] [Algebra o₀ Ω]
    {o : S → Type} [∀ p, CommRing (o p)] [∀ p, Algebra ℤ (o p)]
    [∀ p : S, IsLocalization.AtPrime (o p) (Ideal.span {(((p : Nat.Primes) : ℕ) : ℤ)})]
    [∀ p, Algebra (o p) Ω] {B₀ : ChartBundle o₀ x r E} {Bp : ∀ p, ChartBundle (o p) x r E}
    {i : τ} (hi : x i ≠ 0) (hSR : ∀ p, SameRationalSpan (B₀.lat i) ((Bp p).lat i)) :
    ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing ℤ x i) ∧ (∀ l, c l ∈ chartRing ℤ x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, IsFrameAt (chartRing ℤ x i) r (glueLat B₀ Bp i) (f l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«glueLat_frame» := P2M_GroundTheory_Heights__Heights_Model_glueLat_frame_f0b793a7400f
