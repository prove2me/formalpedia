-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_4
-- name    : OrderedSearchExact.Exact.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:55.482813+00:00
-- url     : https://prove2.me/theorems/93d43533-9f16-46d6-aa8c-0b181c502e47
-- title:
--   Lemma 4.4 — determinant identity and both sufficient conditions
-- statement:
--   Let $n\ge1$, let $h$ be any compactly supported probability density, and let $\alpha,\beta>0$ be finite centers. With $U,V$ as in (20), the hybrid has the identity
--
--   $$q_{S_{\beta e^Y}+A_{\alpha e^Y}}(e^{i\theta})=\mathbb E[\tanh(\beta e^Y/2)U_{\beta e^Y}]\cos^2(n\theta/2)+\mathbb E[\coth(\alpha e^Y/2)U_{\alpha e^Y}]\sin^2(n\theta/2)+\mathbb E[V_{\alpha e^Y}-V_{\beta e^Y}]\sin(n\theta/2)\cos(n\theta/2).$$
--
--   If, at every real angle, the square of the expected difference in the last coefficient is at most four times the product of the two diagonal coefficients, this hybrid is nonnegative. The condition with the centers interchanged likewise implies nonnegativity of $q_{S_{\alpha e^Y}+A_{\beta e^Y}}$. This supplies both parity assignments of the determinant certificate.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - encoding: expectations under a compactly supported probability density → full Lebesgue integrals against a measurable nonnegative density of mass one and almost-sure compact support; reason: the same density class is used; bounded coefficient kernels are integrable against every such density
--   - encoding: Laurent polynomials of degree less than n (no range of n stated in the lemma) → hypothesis 1 ≤ n; reason: degree less than n requires n ≥ 1; n = 0 is not an instance of the source (only the undefined case is excluded)
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.4, p.15 (PDF p.15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Analysis

namespace OrderedSearchExact.Exact

theorem lemma_4_4 (n : ℕ) (hn : 1 ≤ n) (h : ℝ → ℝ) (hh : IsDensity h)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (∀ θ : ℝ, circle (hybrid n h (ENNReal.ofReal β) (ENNReal.ofReal α)) θ =
      diagS n h β θ * Real.cos (n * θ / 2) ^ 2 +
      diagA n h α θ * Real.sin (n * θ / 2) ^ 2 +
      crossTerm n h α β θ * Real.sin (n * θ / 2) * Real.cos (n * θ / 2)) ∧
    (DeterminantCondition n h α β →
      Nonnegative (hybrid n h (ENNReal.ofReal β) (ENNReal.ofReal α))) ∧
    (DeterminantCondition n h β α →
      Nonnegative (hybrid n h (ENNReal.ofReal α) (ENNReal.ofReal β))) := by sorry

end OrderedSearchExact.Exact
