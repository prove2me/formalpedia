-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_15
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:50:58.075081+00:00
-- url     : https://prove2.me/theorems/18517665-ac6e-48ff-a535-b81c06fa5385
-- title:
--   Lemma 15 — Universal interpolation lower bound (29) for every flat target
-- statement:
--   Let $\pi$ be any flat entropy-$k$ target law on $N$ bits, and let $d\ge0$. Then
--   $$\mathcal O_d(\pi)\ge\beta(k,d)=2^{-k}\sum_{j=0}^{\min(k,d)}\binom kj.$$
--   No affine-independence assumption is made. This is a universal interpolation lower bound, including $k=0$, $d=0$ and $d\ge k$.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 15, printed p. 20; PDF p. 22

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_15 {N : ℕ} (k d : ℕ) (π : Word N → ℝ) (hπ : Flat k π) :
    BinomialTail k d ≤ BestOverlap d π := by sorry

end PolynomialSampling137.OneThird.Supplement
