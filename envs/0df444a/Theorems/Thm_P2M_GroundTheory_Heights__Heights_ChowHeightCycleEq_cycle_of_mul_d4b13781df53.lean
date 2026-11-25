-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_cycle_of_mul_d4b13781df53
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_cycle_of_mul_d4b13781df53
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:13.536899+00:00
-- url     : https://prove2.me/theorems/ba4a3388-ef23-4f86-8f59-36fb6e1bc7fd
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Cycle Eq cycle of mul d4b13781df53: P2 M Ground Theory Heights  Heights Chow Height Cycle Eq cycle of mul d4b13781df53
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Cycle Eq cycle of mul d4b13781df53 construction uses the P2 M Ground Theory Heights  Heights Chow Height Cycle Eq cycle of mul d4b13781df53 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L28-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L28-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_cycle_of_mul_d4b13781df53 {K : Type} [Field K] [NumberField K]
    (μ : InfinitePlace K → Measure (Fin (e + 1) × Fin n → ℂ))
    (hμ : ∀ (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (δ₁ δ₂ : ℕ), f ≠ 0 → g ≠ 0 →
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (f * g) (δ₁ + δ₂) =
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ f δ₁ + ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ g δ₂)
    {ι : Type} (Z : ι →₀ ℕ) (f : ι → MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ι → ℕ)
    (hf : ∀ i ∈ Z.support, f i ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z f) (Z.sum fun i m => m * δ i) =
      Z.sum fun i m => (m : ℝ) * ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (f i) (δ i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightCycleEq».«cycle_of_mul» := P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_cycle_of_mul_d4b13781df53
