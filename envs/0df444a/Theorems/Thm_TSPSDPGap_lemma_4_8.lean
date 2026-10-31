-- Prove2me | Theorems.Thm_TSPSDPGap_lemma_4_8
-- name    : TSPSDPGap.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:42.703144+00:00
-- url     : https://prove2.me/theorems/c3f162c3-2806-41c8-afa5-2f8dd3fd8295
-- title:
--   Lemma 4.8 — $\sum_{j=1}^d\cos(\pi jk/d)=(-1+(-1)^k)/2$
-- statement:
--   Let $n$ be even, $d=n/2$, and let $k$ be an integer with $0<k<n$. Then
--   $$
--   \sum_{j=1}^{d}\cos\Bigl(\frac{\pi jk}{d}\Bigr)=\frac{-1+(-1)^k}{2}.
--   $$
--   This consequence of Lagrange's trigonometric identity is used in Lemmas 4.10, 4.19 and Claim 4.17.
--
--   Differences from the source:
--   - encoding: an integer k with 0 < k < n → k : ℕ with 0 < k < n; reason: a positive integer is a natural number; same values
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, Lemma 4.8, p.17

import Mathlib

namespace TSPSDPGap

/-- **Lemma 4.8: a sum of cosines.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, Lemma 4.8, p.17:
"Let n be even and 0 < k < n be an integer. Then Σ_{j=1}^d cos(πjk/d) = (−1 + (−1)^k)/2."

Here `d = n/2` (p.5).

**Formalization Note.** `k : ℕ` with `0 < k < n`; `d = n / 2` is a natural number cast to `ℝ`
(exact since `n` is even). -/
theorem lemma_4_8 (n k : ℕ) (hn : Even n) (hk0 : 0 < k) (hkn : k < n) :
    ∑ j ∈ Finset.Icc 1 (n / 2), Real.cos (Real.pi * j * k / (n / 2 : ℕ)) =
      (-1 + (-1 : ℝ) ^ k) / 2 := by sorry

end TSPSDPGap
