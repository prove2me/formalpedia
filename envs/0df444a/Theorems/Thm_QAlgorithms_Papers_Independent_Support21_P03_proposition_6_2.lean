-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_6_2
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_6_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:40:00.707249+00:00
-- url     : https://prove2.me/theorems/29ca9933-5ee2-4233-860e-6735c4841c69
-- title:
--   Stationarity and positivity of every selected NESS
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$.
--
--   For the NESS assertions assume in addition that $M$ is a complete separable metric space with its Borel sigma algebra, the flow is jointly continuous, and a chosen representative of $\sigma$ is bounded continuous. Assume that the Cesaro family $\{t^{-1}\int_0^t\omega_s\,ds:t\ge1\}$ is precompact for ordinary weak convergence. A selected NESS $\nu$ is a subsequential Cesaro weak limit along times tending to infinity; invariance is not built into this definition.
--
--   For every selected NESS $\nu$,
--   $$(\phi^s)_*\nu=\nu\quad(s\in\mathbb R),\qquad\int_M\sigma\,d\nu\ge0.$$
--
--   The continuous representative of $\sigma$ is used when $\nu$ is singular with respect to the reference law.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 38, Proposition 6.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

section NESS

variable [MetricSpace M] [CompleteSpace M] [TopologicalSpace.SeparableSpace M] [BorelSpace M]

/-- Proposition 6.2, PDF p.38: every selected Cesaro NESS is invariant
and has nonnegative entropy-production expectation. -/
theorem proposition_6_2 (D : TopologicalSystem M) (hNESS4 : CesaroPrecompact D)
    (nu : ProbabilityMeasure M) (hselected : IsSelectedNESS D nu) :
    IsStationary D.toRegularSystem.toNonsingularSystem nu ∧
      0 ≤ ∫ x, D.sigma x ∂(nu : Measure M) := by sorry

end NESS

end QAlgorithms.Papers.Independent.Support21.P03

end
