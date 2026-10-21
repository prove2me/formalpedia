-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_5_3
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_5_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:37:00.164249+00:00
-- url     : https://prove2.me/theorems/910e0117-0dfb-4c83-b4ca-ab207c437b5d
-- title:
--   Invariant normal states have zero production
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$. Assume also (E2), $\sigma\in L^\infty(\omega)$. Let $m\in\mathbb R$ be the finite limit $m=\lim_{t\to\infty}m_t$ required by (E3).
--
--   For every invariant probability measure $\nu\ll\omega$,
--   $$\int_M\sigma\,d\nu=0.$$
--
--   Boundedness modulo $\omega$, combined with absolute continuity, ensures this is an ordinary integrable expectation.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 25, Proposition 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 5.3, PDF p.25: zero production in every invariant normal law. -/
theorem proposition_5_3 (D : RegularSystem M)
    (hE2 : MemLp (continuousSigma D) ∞ (D.omega : Measure M))
    (mean : ℝ) (hE3 : Tendsto (scalarMean D) atTop (𝓝 mean))
    (nu : ProbabilityMeasure M) (hstationary : IsStationary D.toNonsingularSystem nu)
    (hnormal : (nu : Measure M) ≪ (D.omega : Measure M)) :
    (∫ x, continuousSigma D x ∂(nu : Measure M)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
