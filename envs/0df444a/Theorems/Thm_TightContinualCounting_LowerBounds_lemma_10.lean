-- Prove2me | Theorems.Thm_TightContinualCounting_LowerBounds_lemma_10
-- name    : TightContinualCounting.LowerBounds.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:45.964928+00:00
-- url     : https://prove2.me/theorems/95ed9dff-2d5b-4ea3-b7c7-5fa0879f6436
-- title:
--   Lemma 10 — zero-sum tree path martingale
-- statement:
--   Let $T$ be the complete ordered four-ary tree of height $H\ge1$ with arbitrary real edge weights $w$. Suppose each internal node's four outgoing weights sum to zero. Select a uniform leaf $J\in[4^H]$ and let $Z_t$ be the sum of the first $t$ weights on its root path. Then
--
--   $$
--   (Z_t)_{t=0}^H\ \text{is an integrable martingale for its history filtration}.
--   $$
--
--   No uniform bound on the edge weights is assumed. This result applies both to the centered scoring weights and to the uncentered weights used in the accuracy analysis.
--
--   Differences from the source:
--   - encoding: coordinates [d]={1,…,d} → coordinates Fin d={0,…,d−1}; reason: the order-preserving reindexing preserves every interval, vector and finite sum
--   - encoding: complete ordered tree and finite-time martingale → depth/address edge functions, uniform finite counting law, and Mathlib Martingale with explicit integrability; reason: only valid tree addresses enter paths, and Definition 7 includes integrability
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), Lemma 10 p.9; Definition 7 p.6; tree standing assumptions §3.2 p.8

import Mathlib
import Definitions.Def_TightContinualCounting_LowerBounds_sampling

open MeasureTheory

namespace TightContinualCounting.LowerBounds

/-- Lemma 10, p.9: no bounded-weight assumption. -/
theorem lemma_10 (H : ℕ) (hH : 1 ≤ H) (w : ℕ → ℕ → Fin 4 → ℝ)
    (hw : ∀ h < H, ∀ v < 4 ^ h, ∑ i : Fin 4, w h v i = 0) :
    let Z : Fin (H + 1) → Fin (4 ^ H) → ℝ := fun t j => pathSum H w t.val j
    Martingale Z (pathFiltration H w) (uniformFinite (Fin (4 ^ H))) ∧
      ∀ t, Integrable (Z t) (uniformFinite (Fin (4 ^ H))) := by sorry

end TightContinualCounting.LowerBounds
