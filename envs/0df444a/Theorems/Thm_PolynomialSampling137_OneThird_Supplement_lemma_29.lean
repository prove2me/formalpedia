-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_29
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:55:54.984488+00:00
-- url     : https://prove2.me/theorems/84eb348c-9405-43a8-aa22-60f5e585410c
-- title:
--   Lemma 29 — Sharp signed-dyadic gap, equality example, and normalization of all values in [0,1]
-- statement:
--   For every $m\ge0$ and every signed sum $z$ of at most $m$ powers $2^j$, with arbitrary integer exponents,
--   $$|z-1/3|\ge\frac1{3\,4^m}.$$
--   The signed sum $z_m=\sum_{j=1}^m4^{-j}$ attains equality. Moreover, whenever $0\le z\le1$, $z$ is a signed sum of at most $m$ elements of $\{0\}\cup\{2^{-r}:r\ge0\}$. This includes $m=0$ and provides both the sharp gap and the normalization needed for all non-dyadic parameters.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 29, printed p. 37; PDF p. 39

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_Circuits

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_29 (m : ℕ) :
    (∀ z : ℝ, SignedDyadic m z → |z - 1/3| ≥ 1 / (3 * (4 : ℝ) ^ m)) ∧
    (SignedDyadic m (∑ j ∈ Finset.range m, (4 : ℝ) ^ (-((j : ℤ) + 1))) ∧
      |(∑ j ∈ Finset.range m, (4 : ℝ) ^ (-((j : ℤ) + 1))) - 1/3| =
        1 / (3 * (4 : ℝ) ^ m)) ∧
    (∀ z : ℝ, SignedDyadic m z → 0 ≤ z → z ≤ 1 → NormalizedSignedDyadic m z) := by sorry

end PolynomialSampling137.OneThird.Supplement
