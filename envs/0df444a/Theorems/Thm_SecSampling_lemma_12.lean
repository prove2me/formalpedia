-- Prove2me | Theorems.Thm_SecSampling_lemma_12
-- name    : SecSampling.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:50.632813+00:00
-- url     : https://prove2.me/theorems/9f4a5373-1b32-420a-86a7-94928a4961b2
-- title:
--   Lemma 12 — weights by degree: $w_i=p^{i-1}(1-p)$, $w_{ij}=p^{i-1}(1-p)^2$
-- statement:
--   Let $p\in(0,1)$ and fix a size $n$. Let $w_i$ be the total weight of the nodes of size $n$ and degree $i$, and $w_{ij}$ the total weight of the nodes of size $n+1$ and degree $j$ that are in conflict with some node of size $n$ and degree $i$. Then for all $1\le j\le i\le n$,
--   $$w_i=p^{i-1}(1-p),\qquad w_{ij}=(1-p)\,w_i=p^{i-1}(1-p)^2 .$$
--
--   This is the weighted version of Lemma 10: the weight that a node of degree $i$ passes to each of its children is a $(1-p)$ fraction of its own, which is what decides when selecting the children beats selecting the node.
--
--   Differences from the source: none.
-- source:
--   J. Correa, A. Cristi, L. Feuilloley, T. Oosterwijk & A. Tsigonias-Dimitriadis, The Secretary Problem with Independent Sampling, arXiv:2011.07869v1, https://arxiv.org/abs/2011.07869v1, Lemma 12, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_SecSampling_ConflictGraph

open Classical

namespace SecSampling

/-- **Lemma 12** (arXiv:2011.07869v1, p.17). Fix a size `n`; let `w_i` be the total weight of the
nodes of size `n` and degree `i`, and `w_ij` the total weight of the nodes of size `n + 1` and
degree `j` that are in conflict with some node of size `n` and degree `i`. Then for all
`1 ≤ j ≤ i ≤ n`,
`w_i = p^{i−1}(1−p)` and `w_ij = (1−p) w_i = p^{i−1}(1−p)²`. -/
theorem lemma_12 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hin : i ≤ n) :
    ∑ I ∈ (strings n).filter (fun I => degree I = i), weight p I = p ^ (i - 1) * (1 - p) ∧
    ∑ J ∈ (strings (n + 1)).filter
        (fun J => degree J = j ∧ ∃ I ∈ strings n, degree I = i ∧ Conflict I J), weight p J =
      (1 - p) * ∑ I ∈ (strings n).filter (fun I => degree I = i), weight p I ∧
    ∑ J ∈ (strings (n + 1)).filter
        (fun J => degree J = j ∧ ∃ I ∈ strings n, degree I = i ∧ Conflict I J), weight p J =
      p ^ (i - 1) * (1 - p) ^ 2 := by sorry

end SecSampling
