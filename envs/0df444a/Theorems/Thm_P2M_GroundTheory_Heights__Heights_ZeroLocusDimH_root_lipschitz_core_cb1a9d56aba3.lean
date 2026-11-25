-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_root_lipschitz_core_cb1a9d56aba3
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_root_lipschitz_core_cb1a9d56aba3
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:35.429663+00:00
-- url     : https://prove2.me/theorems/ce9cff1e-2c1a-460e-96a1-ed5ce75823ce
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H root lipschitz core cb1a9d56aba3: P2 M Ground Theory Heights  Heights Zero Locus Dim H root lipschitz core cb1a9d56aba3
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H root lipschitz core cb1a9d56aba3 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H root lipschitz core cb1a9d56aba3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L12-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ZeroLocusDimHGeo.lean#L12-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_root_lipschitz_core_cb1a9d56aba3 {E : Type*} [NormedAddCommGroup E] (N : ℕ) (c : ℕ → E → ℂ) (y₀ : E)
    (t₀ : ℂ) (hcont : ∀ k, Continuous (c k))
    (hlip : ∀ k, ∃ L : NNReal, ∃ T ∈ 𝓝 y₀, LipschitzOnWith L (c k) T)
    (hder : ∑ k ∈ range N, c k y₀ * ((k : ℂ) * t₀ ^ (k - 1)) ≠ 0) :
    ∃ δ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ y y' : E, ∀ t t' : ℂ,
      dist y y₀ < δ → dist y' y₀ < δ → dist t t₀ < δ → dist t' t₀ < δ →
      ∑ k ∈ range N, c k y * t ^ k = 0 → ∑ k ∈ range N, c k y' * t' ^ k = 0 →
      ‖t - t'‖ ≤ K * ‖y - y'‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«root_lipschitz_core» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_root_lipschitz_core_cb1a9d56aba3
