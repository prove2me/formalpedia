-- Prove2me | Theorems.Thm_QuantileSPQO_Rate_lemma_3
-- name    : QuantileSPQO.Rate.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:00.140012+00:00
-- url     : https://prove2.me/theorems/bcce7bb1-ebb4-421b-bf25-c0ace6b8da5d
-- title:
--   Lemma 3 — Σ_{i≤k} [∏_{i<j≤k}(1 − a/j^p)] (a/i^p) w(i) = O(k^{−s}) for w(i) = O(1/i^s)
-- statement:
--   Let $a>0$, $p,s\in(0,1)$, $u(i)=a/i^p$, and let $w$ be a sequence with $w(i)>0$ for all $i\ge1$ and $w(i)=O(1/i^s)$. Then
--   $$
--   \sum_{i=1}^{k}\Big[\prod_{j=i+1}^{k}\big(1-u(j)\big)\Big]u(i)\,w(i)=O(k^{-s}).
--   $$
--
--   This weighted-sum estimate is used repeatedly in the rate analysis of Section 4 (Lemmas 4 and 5).
--
--   **Formalization Note** $O(\cdot)$ is the paper's one-sided notion (p. 11): $w(i)=O(1/i^s)$ means $w(i)\le C/i^s$ for all large $i$, and the conclusion means the sum is at most $C'k^{-s}$ for all large $k$.
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, p. 18, Lemma 3

import Mathlib

open Filter Topology

namespace QuantileSPQO.Rate

theorem lemma_3 (a p s : ℝ) (ha : 0 < a) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (w : ℕ → ℝ) (hw_pos : ∀ i : ℕ, 1 ≤ i → 0 < w i)
    (hw : ∃ C : ℝ, ∀ᶠ i : ℕ in atTop, w i ≤ C / (i : ℝ) ^ s) :
    ∃ C' : ℝ, ∀ᶠ k : ℕ in atTop,
      ∑ i ∈ Finset.Icc 1 k, (∏ j ∈ Finset.Ioc i k, (1 - a / (j : ℝ) ^ p)) * (a / (i : ℝ) ^ p) * w i
        ≤ C' * (k : ℝ) ^ (-s) := by sorry

end QuantileSPQO.Rate
