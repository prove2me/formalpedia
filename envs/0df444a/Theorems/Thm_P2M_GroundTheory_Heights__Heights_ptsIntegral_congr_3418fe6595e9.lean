-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ptsIntegral_congr_3418fe6595e9
-- name    : P2M_GroundTheory_Heights__Heights_ptsIntegral_congr_3418fe6595e9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:08.928122+00:00
-- url     : https://prove2.me/theorems/15f632c8-8aa1-564b-8136-dcc588c0fe99
-- title:
--   P2 M Ground Theory Heights  Heights pts Integral congr 3418fe6595e9: P2 M Ground Theory Heights  Heights pts Integral congr 3418fe6595e9
-- statement:
--   The P2 M Ground Theory Heights  Heights pts Integral congr 3418fe6595e9 construction uses the P2 M Ground Theory Heights  Heights pts Integral congr 3418fe6595e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L237-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/MemMCoordIdealIffOfIsWeightedHomogeneous.lean#L237-L252

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
omit [∀ k, Fintype (κ k)]

theorem P2M_GroundTheory_Heights__Heights_ptsIntegral_congr_3418fe6595e9 (P : Ideal (Geo.MRing κ)) {e : ℕ} (φ : Fin e → ((Σ k, κ k) → ℂ) → ℝ)
    {g g' : ((Σ k, κ k) → ℂ) → ℝ} (hg : ∀ z ∈ Geo.mcPts P, g z = g' z) :
    Geo.ptsIntegral P φ g = Geo.ptsIntegral P φ g' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ptsIntegral_congr» := P2M_GroundTheory_Heights__Heights_ptsIntegral_congr_3418fe6595e9
