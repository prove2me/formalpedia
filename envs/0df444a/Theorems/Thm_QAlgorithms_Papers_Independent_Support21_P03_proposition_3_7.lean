-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_3_7
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_3_7
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:34:22.531983+00:00
-- url     : https://prove2.me/theorems/320df6c6-f8e8-4f8f-a565-1c496003f16b
-- title:
--   Discrete entropy-production signs and reversal
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In discrete time set $\sigma=c^1$ and $\sigma_{-1}=\sigma\circ\phi^{-1}$. With extended signed expectations,
--   $$\omega(\sigma)\ge0,\qquad\omega_{-1}(\sigma)\le0.$$
--   If the system is time reversal invariant, $\sigma\circ\vartheta=-\sigma_{-1}$ almost everywhere.
--
--   The instantaneous expectations need not be finite.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 12, Proposition 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.7, PDF p.12. The second expectation is in omega_{-1},
and the TRI identity involves the transported sigma_{-1}. -/
theorem proposition_3_7 (D : NonsingularSystem .discrete M) :
    0 ≤ QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (D.omega : Measure M) (discreteSigma D) ∧
    QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (pushedReference D (-1 : ℤ)) (discreteSigma D) ≤ 0 ∧
    (∀ theta : M ≃ᵐ M, IsTimeReversal D theta →
      ∀ᵐ x ∂(D.omega : Measure M),
        discreteSigma D (theta x) = -discreteSigma D (D.flow (-1 : ℤ) x)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
