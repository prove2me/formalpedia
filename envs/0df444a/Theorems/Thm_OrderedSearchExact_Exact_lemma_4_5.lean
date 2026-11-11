-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_5
-- name    : OrderedSearchExact.Exact.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:01.034304+00:00
-- url     : https://prove2.me/theorems/22842acd-6a06-4c23-9ea8-ad24654b56b6
-- title:
--   Lemma 4.5 — progress at every positive rate
-- statement:
--   Let $n\ge2$, let $h$ be any compactly supported probability density, and let $\alpha>0$ be a center. For every real $r\in[1,3]$,
--
--   $$q_{S_{r\alpha e^Y}+A_{\alpha e^Y}}\ge0,\qquad q_{S_{\alpha e^Y}+A_{r\alpha e^Y}}\ge0.$$
--
--   Consequently, $\Gamma_S(\alpha)\ge3\alpha$ and $\Gamma_A(\alpha)\ge3\alpha$. This gives progress for both update parities at every positive center.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - encoding: expectations under a compactly supported probability density → full Lebesgue integrals against a measurable nonnegative density of mass one and almost-sure compact support; reason: the same density class is used; bounded coefficient kernels are integrable against every such density
--   - encoding: rates in [0,infinity], with limiting endpoints → ENNReal rates with explicit zero and infinity branches; reason: the extended supremum never defaults to a finite real value; the endpoint polynomials are the prescribed limits
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.5, p.16 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Greedy

namespace OrderedSearchExact.Exact

theorem lemma_4_5 (n : ℕ) (hn : 2 ≤ n) (h : ℝ → ℝ) (hh : IsDensity h)
    (α : Rate) (hα : 0 < α) :
    (∀ r : ℝ, 1 ≤ r → r ≤ 3 →
      Nonnegative (hybrid n h (ENNReal.ofReal r * α) α) ∧
      Nonnegative (hybrid n h α (ENNReal.ofReal r * α))) ∧
    3 * α ≤ gammaS n h α ∧ 3 * α ≤ gammaA n h α := by sorry

end OrderedSearchExact.Exact
