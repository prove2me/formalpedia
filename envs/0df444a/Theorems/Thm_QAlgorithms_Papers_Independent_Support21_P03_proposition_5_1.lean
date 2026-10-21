-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_5_1
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_5_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:35:35.193613+00:00
-- url     : https://prove2.me/theorems/6b4add59-b1eb-439d-9bae-4c643591ff69
-- title:
--   Nonnegativity of asymptotic mean entropy production
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$. Assume also (E2), $\sigma\in L^\infty(\omega)$. Let $m\in\mathbb R$ be the finite limit $m=\lim_{t\to\infty}m_t$ required by (E3).
--
--   Then
--   $$m\ge0.$$
--
--   This uses the existing finite asymptotic mean without an ergodicity assumption.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 24, Proposition 5.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 5.1, PDF p.24. E3 pins a finite real limit; no ergodicity. -/
theorem proposition_5_1 (D : RegularSystem M)
    (hE2 : MemLp (continuousSigma D) ∞ (D.omega : Measure M))
    (mean : ℝ) (hE3 : Tendsto (scalarMean D) atTop (𝓝 mean)) :
    0 ≤ mean := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
