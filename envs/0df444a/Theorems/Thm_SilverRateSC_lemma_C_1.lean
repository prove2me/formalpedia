-- Prove2me | Theorems.Thm_SilverRateSC_lemma_C_1
-- name    : SilverRateSC.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:45:01.343395+00:00
-- url     : https://prove2.me/theorems/f09fcca3-a7c0-4853-8d73-648e55f3118c
-- title:
--   Lemma C.1 — two large stepsizes with a small gap, or one dominant stepsize
-- statement:
--   Let $h_1,\dots,h_r\ge0$, where $r\ge1$, and let $S':=\sum_{t=1}^rh_t>0$. At least one of the following holds:
--   1. there exist $1\le i<j\le r$ such that $h_i,h_j\ge S'/(8r^2)$ and $\sum_{t=i+1}^{j-1}h_t\le\min\{h_i,h_j\}$;
--   2. there exists $1\le i\le r$ such that $h_i\ge3S'/4$.
--
--   The lemma guarantees that the second case of the repair checkpoint selection rule can always be carried out.
--
--   Differences from the source:
--   - encoding: h_1, …, h_r → h : ℕ → ℝ read at positions 1, …, r; reason: same data
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma C.1, p.45

import Mathlib

namespace SilverRateSC

/-- **Lemma C.1.** Let `h_1, …, h_r ≥ 0`, where `r ≥ 1`, and let `S' := ∑_{t=1}^r h_t > 0`. At least
one of the following alternatives holds:
1. there exist `1 ≤ i < j ≤ r` such that `h_i, h_j ≥ S'/(8r²)` and
   `∑_{t=i+1}^{j−1} h_t ≤ min{h_i, h_j}`;
2. there exists `1 ≤ i ≤ r` such that `h_i ≥ 3S'/4`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma C.1, p. 45.

**Formalization Note** The stepsizes are `h : ℕ → ℝ` read at positions `1, …, r`. -/
theorem lemma_C_1 (r : ℕ) (hr : 1 ≤ r) (h : ℕ → ℝ) (hh : ∀ t ∈ Finset.Icc 1 r, 0 ≤ h t)
    (hS : 0 < ∑ t ∈ Finset.Icc 1 r, h t) :
    (∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ r ∧
        (∑ t ∈ Finset.Icc 1 r, h t) / (8 * (r : ℝ) ^ 2) ≤ h i ∧
        (∑ t ∈ Finset.Icc 1 r, h t) / (8 * (r : ℝ) ^ 2) ≤ h j ∧
        ∑ t ∈ Finset.Ioo i j, h t ≤ min (h i) (h j)) ∨
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ r ∧ 3 * (∑ t ∈ Finset.Icc 1 r, h t) / 4 ≤ h i := by sorry

end SilverRateSC
