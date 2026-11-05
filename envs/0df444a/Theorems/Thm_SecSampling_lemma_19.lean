-- Prove2me | Theorems.Thm_SecSampling_lemma_19
-- name    : SecSampling.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:33:33.393188+00:00
-- url     : https://prove2.me/theorems/56c8697f-5c70-48c0-a4b2-64cb16ea0aaf
-- title:
--   Lemma 19 — fill-in and $k$-max select the same nodes inside the window (corrected: at size $n+t$ the inclusion is strict only for $n+t>k$)
-- statement:
--   Let $p\in(0,1)$, $k=\lfloor 1/(1-p)\rfloor$, and consider the fill-in strategy and the $k$-max strategy for the window $[n,n+t]$, where at each size $k$-max selects the instances it wins.
--
--   1. If $n>1$: at every size $s$ with $n<s<n+t$ the two select the same nodes; at size $n$ the nodes selected by $k$-max form a strict subset of those selected by fill-in; at size $n+t$ they form a subset, which is strict whenever $n+t>k$.
--   2. If $n=1$: they select the same nodes at size $1$ and at every size $s$ with $1<s<1+t$; at size $1+t$ the nodes selected by $k$-max form a subset of those selected by fill-in, which is strict whenever $t\ge1$ and $1+t>k$.
--
--   Since the weights at one size sum to $1$, fill-in and $k$-max differ in window average by at most $2/(t+1)$.
--
--   Differences from the source:
--   - correction: for sizes s = n and s = n + t, k-max selects a strict subset of the nodes selected by fill-in → strict subset at s = n (n > 1); subset at s = n + t, strict whenever n + t > k (for n = 1: whenever also t ≥ 1); reason: strictness fails at s = n + t when t ≥ 1 and n + t ≤ k: p = 2/3 (k = 3), window [2, 3]: fill-in selects all of size 2, so at size 3 the non-removed nodes are 110, 101, 011, 111, all of degree ≤ 3, and k-max wins all four. For n + t > k the node 01ⁿ⁺ᵗ⁻¹ is selected by fill-in and lost by k-max, so the printed strictness stands
--   - reading: if n = 1, they select the same set of nodes for size s = n = 1 as well → for n = 1: equal at s = 1 and at 1 < s < 1 + t; at 1 + t a subset, strict whenever t ≥ 1 and 1 + t > k; reason: "as well" adds size 1 to the conclusions of the n > 1 case
--   - reading: for every size s ≠ n, n + t → for every size n < s < n + t; reason: fill-in selects nothing outside the window, so the claim concerns the sizes of the window; k-max "selects" the instances it wins
--   - reading: the player wins if she stops on the last 0 of the sequence (Definition 1) → a string with no 0 is won by every strategy; reason: the page leaves this case open; p.2 declares it a win by vacuity for AOSp, and it changes the performance at size n by pⁿ only
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 19, pp.23–24 (PDF pp.24–25)

import Mathlib
import Definitions.Def_SecSampling_FractionalSelection

open Classical

namespace SecSampling

/-- **Lemma 19** (arXiv:2011.07869v1, pp.23–24), corrected. Consider the fill-in strategy and the
k-max algorithm (`k = ⌊1/(1−p)⌋`) for the window `[n, n + t]`; at each size `s`, k-max selects the
nodes it wins in.

* If `n > 1`: for every size `n < s < n + t` the two select the same set of nodes; at size `s = n`
  k-max selects a strict subset of the nodes selected by fill-in; at size `s = n + t` it selects a
  subset, and a strict subset as soon as `n + t > k`.
* If `n = 1`: they select the same set at size `s = 1` and at every size `1 < s < 1 + t`, and at
  size `1 + t` k-max selects a subset, and a strict subset as soon as `t ≥ 1` and `1 + t > k`.

The printed lemma says "strict subset" at `s = n + t` for every window; that fails when
`t ≥ 1` and `n + t ≤ k` (p = 2/3, window [2, 3]), so the strictness is kept for `n + t > k`. -/
theorem lemma_19 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n t : ℕ) :
    (1 < n →
      (∀ s : ℕ, n < s → s < n + t →
        (strings s).filter (fun I => winLZ (kmaxLZ p) I = 1) = fillSet p n t s) ∧
      (strings n).filter (fun I => winLZ (kmaxLZ p) I = 1) ⊂ fillSet p n t n ∧
      (strings (n + t)).filter (fun I => winLZ (kmaxLZ p) I = 1) ⊆ fillSet p n t (n + t) ∧
      (kOf p < n + t →
        (strings (n + t)).filter (fun I => winLZ (kmaxLZ p) I = 1) ⊂ fillSet p n t (n + t))) ∧
    (n = 1 →
      (∀ s : ℕ, n ≤ s → s < n + t →
        (strings s).filter (fun I => winLZ (kmaxLZ p) I = 1) = fillSet p n t s) ∧
      (strings n).filter (fun I => winLZ (kmaxLZ p) I = 1) = fillSet p n t n ∧
      (strings (n + t)).filter (fun I => winLZ (kmaxLZ p) I = 1) ⊆ fillSet p n t (n + t) ∧
      (0 < t → kOf p < n + t →
        (strings (n + t)).filter (fun I => winLZ (kmaxLZ p) I = 1) ⊂ fillSet p n t (n + t))) := by sorry

end SecSampling
