-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_lemma_2
-- name    : PolynomialSampling137.OneThird.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T10:27:21.435188+00:00
-- url     : https://prove2.me/theorems/09908547-c99d-41c9-85e4-b3c62e2577a9
-- title:
--   Lemma 2 — weighted affine-cube lower bound
-- statement:
--   Let $s\ge0$, $t\ge1$ be integers and let $f:\mathbb F_2^s\to[0,1]$. With independent uniform base point $x$ and directions $h_j$, and $K=2^t$,
--
--   $$\mathbb E_{x,h_1,\ldots,h_t}\prod_{v\in\mathbb F_2^t}f\!\left(x+\sum_jv_jh_j\right)\ge(\mathbb E f)^K.$$
--
--   The product retains all labels, even for a degenerate cube. This lower bound supplies the cube-weight estimate for amplification; the pointwise interval restriction is part of the statement.
--
--   Differences from the source:
--   - encoding: independent uniform cube parameters and the product over all vertex labels → nested finite averages on Fin-indexed binary words and a product over every label; reason: all parameters are sampled without a rank condition, and repeated points retain their multiplicities
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 2, printed p. 10 / PDF p. 12

import Definitions.Def_PolynomialSampling137_OneThird_AffineCubes

namespace PolynomialSampling137.OneThird

/-- Zhong, Lemma 2: uniform cubes include all degeneracies and repeated labels. -/
theorem lemma_2 (s t : ℕ) (ht : 1 ≤ t) (f : Word s → ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    (uniformAverage f) ^ (2 ^ t) ≤ cubeAverage t f := by sorry

end PolynomialSampling137.OneThird
