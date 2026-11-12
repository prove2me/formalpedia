-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_4_3
-- name    : RelatedSchedFPTAS796.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:48.662555+00:00
-- url     : https://prove2.me/theorems/412bec71-690d-4db7-bfc6-261f99a4d800
-- title:
--   Lemma 4.3 — a random $k$-partition puts at most $2|Y|/k$ of $Y$ in each part when $|Y|\ge3k\log(k/q)$
-- statement:
--   Let $X$ be a multiset, $k>0$ an integer and $q\in(0,1)$, and let $X_1,\dots,X_k$ be a random partition of $X$. For any $Y\subseteq X$ with $|Y|\ge3k\log(k/q)$, with probability at least $1-q$,
--   $$|Y\cap X_j|\ \le\ \frac{2|Y|}{k}\quad\text{for all } j\in\{1,\dots,k\},$$
--   with $\log$ base 2.
--
--   In the proof of Lemma 4.4 it bounds the work of the large-scale machines $d'+1,\dots,d$ inside every first-layer part, which is what makes the recursive targets $u_i$ sufficient.
--
--   Differences from the source:
--   - encoding: a multiset $X$ of integers and $Y\subseteq X$ → the $N$ occurrences of $X$ and a set $Y$ of occurrences; reason: the integer values play no role in the statement
--   - encoding: a random partition of $X$ → a uniformly random map from the occurrences to the parts, probability = fraction of maps; reason: Algorithm 1, lines 2 and 8: each occurrence independently and uniformly into a part
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.10, Lemma 4.3 (proof p.10)

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_RandomPartition

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 4.3**, p.10. Let `X` be a multiset (of `N` occurrences), `k > 0` an integer and
`q ∈ (0, 1)`. Let `X_1, …, X_k` be a random partition of `X`. For any `Y ⊆ X` with
`|Y| ≥ 3k log(k/q)`, with probability at least `1 − q`, `|Y ∩ X_j| ≤ 2|Y|/k` for all
`j ∈ {1, …, k}` (`log` base 2). -/
theorem lemma_4_3 (N k : ℕ) (hk : 0 < k) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (Y : Finset (Fin N)) (hY : 3 * k * Real.logb 2 (k / q) ≤ Y.card) :
    1 - q ≤ partitionProb N k
      (fun f => ∀ j, (partCount f Y j : ℝ) ≤ 2 * Y.card / k) := by sorry

end RelatedSchedFPTAS796.Main
