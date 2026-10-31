-- Prove2me | Theorems.Thm_TSPSDPGap_lemma_4_19
-- name    : TSPSDPGap.lemma_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:24.171976+00:00
-- url     : https://prove2.me/theorems/e14c698d-eccc-4da2-9dd5-9d18de5ba35e
-- title:
--   Lemma 4.19 — $\sum_{i=1}^d\cos(\pi ij/d)\cos(\pi ik/d)\ge-\mathbb 1\{j-k\text{ odd}\}$
-- statement:
--   For every natural number $d$ and all integers $j,k$,
--   $$
--   \sum_{i=1}^{d}\cos\Bigl(\frac{\pi ij}{d}\Bigr)\cos\Bigl(\frac{\pi ik}{d}\Bigr)\ \ge\ -\mathbb 1\{j-k\ \text{odd}\}.
--   $$
--   It bounds the cosine products in the lower bound $a^{(k)}\ge-g/(n-g)$ of Proposition 4.14.
--
--   **Formalization Note** For $d=0$ the sum is empty.
--
--   Differences from the source:
--   - generalization: d = n/2 and indices 1 ≤ j ≤ g − 1, 1 ≤ k ≤ n − 1 of the surrounding proof → every d ∈ ℕ and all integers j, k; reason: the printed lemma states no range and its proof's case analysis covers every case; specializes to the paper's use
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Lemma 4.19, p.24

import Mathlib

namespace TSPSDPGap

/-- **Lemma 4.19: a lower bound on a sum of cosine products.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Lemma 4.19, p.24:
"Σ_{i=1}^d cos(πij/d) cos(πik/d) ≥ −𝟙{j−k odd}."

**Formalization Note.** Stated for every natural `d` and all integers `j, k` (the paper's
context is `d = n/2`, `1 ≤ j ≤ g − 1`, `1 ≤ k ≤ n − 1`; its proof covers every case).
`𝟙{j−k odd}` is `if Odd (j - k) then 1 else 0`. -/
theorem lemma_4_19 (d : ℕ) (j k : ℤ) :
    -(if Odd (j - k) then (1 : ℝ) else 0) ≤
      ∑ i ∈ Finset.Icc 1 d, Real.cos (Real.pi * i * j / d) * Real.cos (Real.pi * i * k / d) := by sorry

end TSPSDPGap
