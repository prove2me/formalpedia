-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_chartForm_22a5052f5383
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_chartForm_22a5052f5383
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:54.035002+00:00
-- url     : https://prove2.me/theorems/00e45858-29ba-4d5d-8013-fe0928191665
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Section exists chart Form 22a5052f5383: P2 M Ground Theory Heights  Heights Chart Lat Section exists chart Form 22a5052f5383
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Section exists chart Form 22a5052f5383 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Section exists chart Form 22a5052f5383 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L106-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L106-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_chartForm_22a5052f5383 (y : Coord n → Ω) (a : ι → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ Geo.chartLat (ι := blockIdx n) y a τ) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (d δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      (∀ k, (δ k : ℤ) = (τ • a) k + d k) ∧ aeval y e = s * ∏ k, y ⟨k, c k⟩ ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatSection».«exists_chartForm» := P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_chartForm_22a5052f5383
