-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_multiplicativeDomainBimodule
-- name    : QAlgorithms.Papers.Independent.Next46.P43.multiplicativeDomainBimodule
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:42:10.315178+00:00
-- url     : https://prove2.me/theorems/5bd67c67-4f45-457a-88ba-4d01d1f5bfa6
-- title:
--   Lemma 5: multiplicative domain and bimodule identities
-- statement:
--   Let $N,M$ be complex unital C*-algebras and let $\sigma:N\to M$ be complex-linear, unital and 2-positive. Define
--
--   $$
--   N_\sigma=\{a:\ \sigma(a^*a)=\sigma(a)^*\sigma(a),\quad
--   \sigma(aa^*)=\sigma(a)\sigma(a)^*\}.
--   $$
--
--   Then $N_\sigma$ is a closed unital star subalgebra of $N$, and for every $a\in N_\sigma$ and $b\in N$,
--
--   $$
--   \sigma(ab)=\sigma(a)\sigma(b),\qquad \sigma(ba)=\sigma(b)\sigma(a).
--   $$
--
--   These are the multiplicative-domain bimodule identities. Complete positivity and von Neumann normality are not added as hypotheses.
--
--   **Formalization Note** Equation (13) prints the two right-hand products in reversed adjoint order. The statement corrects their order according to the Schwarz inequality used in the proof; independent moderation is required.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 11, Lemma 5: multiplicative domain and bimodule identities

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Lemma 5, PDF pp.11–12, (13)–(14). Printed: sigma(a*a)=sigma(a)sigma(a)*
and sigma(aa*)=sigma(a)*sigma(a). Changed: the first right side is sigma(a)*sigma(a)
and the second is sigma(a)sigma(a)*. Why: the proof uses the usual Schwarz
inequality; the printed set even for the identity map consists of normal
elements and is not a subalgebra. This correction needs independent moderation.
Both bimodule identities hold for every b, under 2-positivity alone. -/
theorem multiplicativeDomainBimodule
    {N M : Type*} [CStarAlgebra N] [CStarAlgebra M]
    [PartialOrder N] [PartialOrder M] [StarOrderedRing N] [StarOrderedRing M]
    (sigma : N →ₗ[ℂ] M) (hSigma : IsCStarCoarseGraining sigma) :
    ∃ D : StarSubalgebra ℂ N, (D : Set N) = MultiplicativeDomain sigma ∧
      IsClosed (D : Set N) ∧
      ∀ a ∈ D, ∀ b : N,
        sigma (a * b) = sigma a * sigma b ∧
        sigma (b * a) = sigma b * sigma a := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
