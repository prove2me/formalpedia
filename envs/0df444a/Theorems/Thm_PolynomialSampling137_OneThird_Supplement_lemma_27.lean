-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_lemma_27
-- name    : PolynomialSampling137.OneThird.Supplement.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:53:48.038193+00:00
-- url     : https://prove2.me/theorems/02944ac9-7eee-45be-bb24-58ba561d99b8
-- title:
--   Lemma 27 — Inverse-line small bias for every nonzero binary character
-- statement:
--   Let $K=\mathbb F_{2^k}$, $k\ge1$, and let $E/K$ have degree $h\ge2$. Let $\theta\in E$ have degree $h$ over $K$, and fix any binary linear identification $E\simeq\mathbb F_2^{hk}$. For uniform $X\in K$, the law of $(\theta+X)^{-1}$ has support size $2^k$ and satisfies
--   $$\left|\mathbb E(-1)^{\lambda\cdot(\theta+X)^{-1}}\right|\le 2h\,2^{-k/2}\quad(\lambda\ne0).$$
--   Every nonzero binary character is covered, without a restriction to $K$-linear characters or to one extension degree. This supplies small bias for the active coordinates of the inverse-line construction.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Lemma 27, printed p. 34; PDF p. 36

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_BinaryFields

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem lemma_27 (k h : ℕ) (hh : 2 ≤ h)
    (K E : Type*) [Field K] [Fintype K] [Field E] [Fintype E]
    [Algebra (ZMod 2) K] [Algebra (ZMod 2) E] [Algebra K E]
    (hcard : Fintype.card K = 2 ^ k) (hdim : Module.finrank K E = h)
    (e : E ≃ₗ[ZMod 2] Word (h * k)) (θ : E)
    (hθ : (minpoly K θ).natDegree = h) :
    (Finset.univ.image (InverseLine (K := K) e θ)).card = 2 ^ k ∧
    SmallBias (UniformImage (InverseLine (K := K) e θ))
      (2 * h * (2 : ℝ) ^ (-(k : ℝ)/2)) := by sorry

end PolynomialSampling137.OneThird.Supplement
