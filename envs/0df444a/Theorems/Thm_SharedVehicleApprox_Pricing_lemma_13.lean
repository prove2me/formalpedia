-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_lemma_13
-- name    : SharedVehicleApprox.Pricing.lemma_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:13.783264+00:00
-- url     : https://prove2.me/theorems/9094baef-1dd6-47d0-a29c-7b7ad26cc694
-- title:
--   Lemma 13, p. 17 — a weighted bipartite graph between S_{n,m} and S_{n,m−1}: weights on neighbours only, totals (m+n−1)/m and 1
-- statement:
--   Let $m\ge1$. Call $y\in S_{n,m-1}$ a neighbour of $x\in S_{n,m}$ if $x=y+e_i$ for some node $i$. There are nonnegative weights $\omega_{xy}$, $x\in S_{n,m}$, $y\in S_{n,m-1}$, such that
--
--   1. $\omega_{xy}\ne0$ only if $y$ is a neighbour of $x$;
--   2. for every $y\in S_{n,m-1}$, $\displaystyle\sum_{x\in S_{n,m}}\omega_{xy}=\frac{m+n-1}{m}$;
--   3. for every $x\in S_{n,m}$, $\displaystyle\sum_{y\in S_{n,m-1}}\omega_{xy}=1$.
--
--   This combinatorial fact drives the bound $G_m\le r_{\max}\frac{m+n-1}{m}G_{m-1}$ of Lemma 14.
--
--   Differences from the source:
--   - reading: "weighted bipartite graph" → nonnegative weights ω_xy; reason: the construction's weights x_i/m are nonnegative and Lemma 14's inequality step needs ω ≥ 0; this is the stronger reading
--   - reading: "y + e_i ∈ S_{n,m} ∀i ∈ {1, n}" → x = y + e_i for some i ∈ Fin n (every node); reason: {1, n} is a typo for [n] = {1, …, n}: the proof uses every i ∈ [n]
--   - encoding: a graph on S_{n,m} ∪ S_{n,m−1} → a weight function ω on pairs (x, y), with 1 ≤ m; reason: a weighted bipartite graph is its weight function; S_{n,m−1} needs m ≥ 1
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 17 (PDF 18), Lemma 13

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Lemma 13, p. 17: for `m ≥ 1` there are nonnegative weights `ω_xy` on
`S_{n,m} × S_{n,m−1}`, nonzero only when `x = y + e_i` for some node `i`, whose total at every
`y ∈ S_{n,m−1}` is `(m+n−1)/m` and whose total at every `x ∈ S_{n,m}` is `1`. -/
theorem lemma_13 {n m : ℕ} (hm : 1 ≤ m) :
    ∃ ω : (Fin n → ℕ) → (Fin n → ℕ) → ℝ,
      (∀ x y, 0 ≤ ω x y) ∧
      (∀ x ∈ states n m, ∀ y ∈ states n (m - 1), ω x y ≠ 0 → ∃ i, x = y + Pi.single i 1) ∧
      (∀ y ∈ states n (m - 1), ∑ x ∈ states n m, ω x y = ((m : ℝ) + n - 1) / m) ∧
      (∀ x ∈ states n m, ∑ y ∈ states n (m - 1), ω x y = 1) := by sorry

end SharedVehicleApprox.Pricing
