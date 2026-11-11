-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_eq_10
-- name    : PolynomialSampling137.OneThird.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T10:26:11.920453+00:00
-- url     : https://prove2.me/theorems/510480a1-30d3-4805-9f92-3968aee59a35
-- title:
--   §2.3 Eq. (10) — coordinate-test bound
-- statement:
--   Let $R$ be a probability law on a finite product of $n$ coordinate spaces, let $R_i$ be its marginals, and let $M=\bigotimes_iM_i$ be a product reference. For a nonnegative range length $a$, suppose every real coordinate test $g_i$ has range of length at most $a$. Then
--
--   $$\left|\sum_i\bigl(\mathbb E_{R_i}g_i-\mathbb E_{M_i}g_i\bigr)\right|\le a\sqrt{\frac n2D(R\Vert M)}.$$
--
--   The inequality is interpreted in extended nonnegative reals. If $a=0$, the expectation difference is zero even when KL is infinite. If $n=0$, both sides are zero. For positive $a,n$ and infinite KL, the right side is infinite. No finiteness or absolute-continuity hypothesis narrows this statement. The referenced bounded-expectation Pinsker theorem is a proof ingredient for the finite-KL case.
--
--   Differences from the source:
--   - encoding: finite probability laws, their actual marginals, and product references → Mathlib PMFs on finite heterogeneous coordinate types, real point masses, and PMF.map marginals; reason: zeros are allowed; normalized laws force the required carriers to be nonempty without an extra hypothesis
--   - encoding: KL in natural logarithms, with positive infinity when absolute continuity fails → ENNReal finite-sum KL with an explicit absolute-continuity branch; reason: the finite sum is nonnegative on probability laws; infinity is preserved and never converted to real zero
--   - encoding: range length at most a and a square-root bound, including zero-range tests → a nonnegative real a, pairwise test differences bounded by a, and ENNReal power one-half with zero times infinity equal to zero; reason: on finite nonempty carriers pairwise differences characterize range length; the extended expression retains every finite and infinite KL case
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §2.3 Eq. (10), printed p. 9 / PDF p. 11

import Definitions.Def_PolynomialSampling137_OneThird_FiniteProbability
open scoped ENNReal NNReal

namespace PolynomialSampling137.OneThird

/-- Zhong, §2.3 Eq. (10). Extended multiplication gives 0 * infinity = 0,
so zero-range tests and the empty coordinate family retain their direct meaning. -/
theorem eq_10 (n : ℕ) (Ω : Fin n → Type*) [∀ i, Fintype (Ω i)]
    (R : PMF (∀ i, Ω i)) (M : ∀ i, PMF (Ω i))
    (a : ℝ≥0) (g : ∀ i, Ω i → ℝ)
    (hg : ∀ i x y, |g i x - g i y| ≤ (a : ℝ)) :
    ENNReal.ofReal |∑ i, (expectation (marginal R i) (g i) - expectation (M i) (g i))| ≤
      (a : ℝ≥0∞) *
        (ENNReal.ofReal ((n : ℝ) / 2) * relativeEntropy (mass R) (productMass M)) ^
          (1 / 2 : ℝ) := by sorry

end PolynomialSampling137.OneThird
