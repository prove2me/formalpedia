-- Prove2me | Theorems.Thm_RankCutFacility_Shifted_later_rank_grid
-- name    : RankCutFacility.Shifted.later_rank_grid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:06.404019+00:00
-- url     : https://prove2.me/theorems/873525f5-47ed-45fd-94df-1e5d6c75f54c
-- title:
--   Lemma 4.4 — Finite later-rank grid estimate
-- statement:
--   Let $n\ge1$, $1\le T<n$, $\mu,\delta\in(0,1]$, and $x\ge0$. For every rank $j$, use exactly $\lambda_j=\min\{1,(j-1+\delta)/(n\mu)\}$.
--
--   Lemma 4.4. For T < n and x ≥ 0,
--   $$
--   \frac1{n-T}\sum_{j=T+1}^n(1-\lambda_j)\mathbf1\{\lambda_j\le x\}\le\mu(x-\lambda_T)^+.\tag{14}
--   $$
--
--   This bounds the complete later-rank grid, with equality included at a threshold.
--
--   Differences from the source: none.
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), Lemma 4.4, printed p. 11 (PDF p. 13), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf

import Definitions.Def_RankCutFacility_Shifted_Analysis

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
theorem later_rank_grid (n T : ℕ) (hT : 1 ≤ T) (hTn : T < n)
    (μ δ x : ℝ) (hμ : 0 < μ ∧ μ ≤ 1) (hδ : 0 < δ ∧ δ ≤ 1) (hx : 0 ≤ x) :
    (∑ j ∈ Finset.Icc (T+1) n,
      if penalty n j μ δ ≤ x then 1 - penalty n j μ δ else 0) / ((n-T : ℕ) : ℝ) ≤
      μ * positivePart (x - penalty n T μ δ) := by sorry
end RankCutFacility.Shifted
