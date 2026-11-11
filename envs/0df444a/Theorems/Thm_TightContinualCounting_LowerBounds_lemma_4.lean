-- Prove2me | Theorems.Thm_TightContinualCounting_LowerBounds_lemma_4
-- name    : TightContinualCounting.LowerBounds.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:11.463464+00:00
-- url     : https://prove2.me/theorems/683b7c66-7fcb-4afa-a61d-67dd84f1934f
-- title:
--   Lemma 4 — midrange stability for nested coordinate sets
-- statement:
--   For $v\in\mathbb R^d$ and nonempty coordinate sets $u'\subseteq u\subseteq[d]$, let $c_u$ be the midrange and $r_u$ the range. Then
--
--   $$
--   |c_{u'}(v)-c_u(v)|\le\frac{r_u(v)-r_{u'}(v)}2.
--   $$
--
--   This bounds how much the midrange probe can move when passing to a subset, in terms of the loss of range. It supports the midrange branch of the accuracy bound.
--
--   Differences from the source:
--   - encoding: coordinates [d]={1,…,d} → coordinates Fin d={0,…,d−1}; reason: the order-preserving reindexing preserves every interval, vector and finite sum
-- source:
--   Charlie Harrison, Ethan Leeman, Tight Lower Bounds for Differentially Private Continual Counting, STOC 2027 submission #1453 (October 2026), Lemma 4 p.5

import Mathlib
import Definitions.Def_TightContinualCounting_LowerBounds_probes

namespace TightContinualCounting.LowerBounds

/-- Lemma 4 (Midrange stability), p.5. -/
theorem lemma_4 {d : ℕ} (v : Fin d → ℝ) (u u' : Finset (Fin d))
    (hu' : u'.Nonempty) (hsub : u' ⊆ u) :
    |midProbe u' v - midProbe u v| ≤ (rangePotential u v - rangePotential u' v) / 2 := by sorry

end TightContinualCounting.LowerBounds
