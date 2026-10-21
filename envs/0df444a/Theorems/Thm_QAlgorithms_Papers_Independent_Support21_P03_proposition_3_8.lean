-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_3_8
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_3_8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:34:52.101707+00:00
-- url     : https://prove2.me/theorems/1da5efa3-41c5-4573-b7b7-0dd29e21d29e
-- title:
--   Continuous entropy production and density representatives
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$.
--
--   There is a simultaneous choice $\rho_t$ of measurable representatives of $d\omega_t/d\omega$ such that $t\mapsto\rho_t(x)$ is locally absolutely continuous for every $x$, and, for $\omega$-almost every $x$ and Lebesgue-almost every $t$,
--   $$\frac{d}{dt}\rho_t(x)=\rho_t(x)\sigma_{-t}(x).$$
--   For every real $t$, in the quotient of observables,
--   $$\frac{d\omega_t}{d\omega}=\exp\left(\int_0^t\sigma_{-s}\,ds\right),\qquad c^t=A_t.$$
--   Furthermore $\omega(\sigma)=0$. If the system is time reversal invariant then $\sigma\circ\vartheta=-\sigma$ almost everywhere.
--
--   The regularity assertion concerns chosen representatives, while the integral identities are identities of equivalence classes.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 12, Proposition 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 3.8, PDF pp.12--13. Part (1) chooses simultaneous RN
representatives; it does not assert regularity of every representative.
All four clauses are retained; TRI is required only in part (4). -/
theorem proposition_3_8 (D : RegularSystem M) :
    (∃ rho : ℝ → M → ℝ,
      (∀ t, Measurable (rho t)) ∧
      (∀ t, ∀ᵐ x ∂(D.omega : Measure M), rho t x = referenceRNReal D.toNonsingularSystem t x) ∧
      (∀ x, LocallyAbsolutelyContinuous (fun t => rho t x)) ∧
      (∀ᵐ x ∂(D.omega : Measure M), ∀ᵐ t : ℝ ∂volume,
        HasDerivAt (fun s => rho s x)
          (rho t x * continuousSigma D (D.flow (-t) x)) t)) ∧
    (∀ t : ℝ, ∀ᵐ x ∂(D.omega : Measure M),
      referenceRNReal D.toNonsingularSystem t x =
        Real.exp (∫ s in 0..t, continuousSigma D (D.flow (-s) x)) ∧
      entropyCocycle D.toNonsingularSystem t x = integratedSigma D t x) ∧
    (∫ x, continuousSigma D x ∂(D.omega : Measure M)) = 0 ∧
    (∀ theta : M ≃ᵐ M, IsTimeReversal D.toNonsingularSystem theta →
      ∀ᵐ x ∂(D.omega : Measure M), continuousSigma D (theta x) = -continuousSigma D x) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
