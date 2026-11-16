-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_18
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:51:58.978867+00:00
-- url     : https://prove2.me/theorems/30fbbd60-44cc-4d23-8554-e37064b71c69
-- title:
--   Lemma 18 — Variance-sensitive relative-entropy expectation bound with exact constants
-- statement:
--   On a finite product space let $M=\bigotimes_iM_i$ be strictly positive. Let $G(y)=\sum_i g_i(y_i)$, where $\mathbb E_{M_i}g_i=0$ and $|g_i|\le1$. Set $V=\sum_i\mathbb E_{M_i}g_i^2$. For every probability law $R\ll M$, writing $D=D_{\rm KL}(R\Vert M)$ with natural logarithms,
--   $$\mathbb E_R G\le2\sqrt{VD}+D.$$
--   The cases $V=0$, $D=0$, and an empty coordinate product are included. Strict positivity makes the finite-law KL finite before its conversion to a real number. This variance-sensitive estimate supports the explicit AND-product exponent.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 18, printed p. 22; PDF p. 24

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_18 {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, Fintype (Ω i)] (M : ∀ i, PMF (Ω i))
    (hpositive : ∀ i x, 0 < mass (M i) x) (g : ∀ i, Ω i → ℝ)
    (hzero : ∀ i, expectation (M i) (g i) = 0)
    (hbounded : ∀ i x, |g i x| ≤ 1) (R : PMF (∀ i, Ω i))
    (hac : ∀ y, productMass M y = 0 → mass R y = 0) :
    expectation R (fun y => ∑ i, g i (y i)) ≤
      2 * Real.sqrt ((∑ i, expectation (M i) (fun x => g i x ^ 2)) *
        (relativeEntropy (mass R) (productMass M)).toReal) +
        (relativeEntropy (mass R) (productMass M)).toReal := by sorry

end PolynomialSampling137.OneThird.Supplement
