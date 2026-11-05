-- Prove2me | Theorems.Thm_SecSampling_lemma_10
-- name    : SecSampling.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:13.945065+00:00
-- url     : https://prove2.me/theorems/ec2bdb80-14a2-42b5-b0af-bf927d79ec01
-- title:
--   Lemma 10 — degree distribution and the degrees of the children
-- statement:
--   Consider the $2^n$ nodes of size $n$ in the conflict graph.
--
--   1. For every $i\in\{1,\dots,n-1\}$ there are exactly $2^{n-i}$ nodes of degree $i$.
--   2. Exactly one node has degree $n$.
--   3. A node of degree $d$ has exactly one child of degree $i$ for every $i\in\{1,\dots,d\}$.
--
--   (Half of the nodes have degree one, a quarter degree two, and so on; the remaining node of size $n$, the all-ones string, has degree $0$.) Every subtree of the conflict graph is thus determined by the degree of its root, which is what makes the weighted counting of Lemma 12 possible.
--
--   **Formalization Note.** The lemma's degree is called $d$ here; it is unrelated to $\lfloor 1/(1-p)\rfloor$.
--
--   Differences from the source: none.
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 10, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

open Classical

namespace SecSampling

/-- **Lemma 10** (arXiv:2011.07869v1, p.16). Consider all `2ⁿ` nodes of size `n`. For every
`i ∈ {1, …, n−1}` there are `2^{n−i}` nodes of degree `i`, and one node has degree `n`. Moreover,
a node with degree `d` has exactly one child of degree `i` for every `i ∈ {1, …, d}`.

**Formalization Note.** The lemma's degree bound is called `d` here (the paper's `k`, a bound
variable unrelated to `⌊1/(1−p)⌋`). -/
theorem lemma_10 (n : ℕ) :
    (∀ i : ℕ, 1 ≤ i → i < n → ((strings n).filter (fun I => degree I = i)).card = 2 ^ (n - i)) ∧
    ((strings n).filter (fun I => degree I = n)).card = 1 ∧
    (∀ I : List Bool, ∀ i : ℕ, 1 ≤ i → i ≤ degree I →
      ((strings (I.length + 1)).filter (fun J => Edge I J ∧ degree J = i)).card = 1) := by sorry

end SecSampling
