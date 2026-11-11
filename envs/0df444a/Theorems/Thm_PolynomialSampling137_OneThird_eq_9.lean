-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_eq_9
-- name    : PolynomialSampling137.OneThird.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T10:26:08.121136+00:00
-- url     : https://prove2.me/theorems/87f6557a-e4e4-42e6-905a-24bcb2783458
-- title:
--   §2.3 Eq. (9) — total-correlation KL decomposition
-- statement:
--   Let $R$ be any probability law on a finite product $\prod_{i=1}^n\Omega_i$, let $R_i$ be its actual marginals, and let $M_i$ be arbitrary coordinate probability laws. Then, in extended nonnegative reals,
--
--   $$D\!\left(R\middle\Vert\bigotimes_iM_i\right)=\operatorname{Tc}(R)+\sum_iD(R_i\Vert M_i),\qquad\operatorname{Tc}(R)=D\!\left(R\middle\Vert\bigotimes_iR_i\right).$$
--
--   The equality includes laws with zeros and infinite divergence, and the empty coordinate family. It isolates marginal divergence from dependence; $R$ need not be a product law.
--
--   Differences from the source:
--   - encoding: finite probability laws, their actual marginals, and product references → Mathlib PMFs on finite heterogeneous coordinate types, real point masses, and PMF.map marginals; reason: zeros are allowed; normalized laws force the required carriers to be nonempty without an extra hypothesis
--   - encoding: KL in natural logarithms, with positive infinity when absolute continuity fails → ENNReal finite-sum KL with an explicit absolute-continuity branch; reason: the finite sum is nonnegative on probability laws; infinity is preserved and never converted to real zero
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §2.3 Eq. (9), printed p. 9 / PDF p. 11

import Definitions.Def_PolynomialSampling137_OneThird_FiniteProbability

namespace PolynomialSampling137.OneThird

/-- Zhong, §2.3 Eq. (9): equality in extended nonnegative reals, including infinite KL. -/
theorem eq_9 (n : ℕ) (Ω : Fin n → Type*) [∀ i, Fintype (Ω i)]
    (R : PMF (∀ i, Ω i)) (M : ∀ i, PMF (Ω i)) :
    relativeEntropy (mass R) (productMass M) =
      totalCorrelation R + ∑ i, relativeEntropy (mass (marginal R i)) (mass (M i)) := by sorry

end PolynomialSampling137.OneThird
