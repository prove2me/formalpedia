-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_5_13
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_5_13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:38:46.301345+00:00
-- url     : https://prove2.me/theorems/a32c4a12-4f22-4726-a8b0-1f64af9b9e6b
-- title:
--   Structure of the asymptotic ES pressure
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$.
--
--   Assume time reversal invariance and that $e(\alpha)=\lim_{t\to\infty}e_t(\alpha)/t$ exists in the extended reals for every $\alpha$. Set $\Sigma^+=\limsup_{t\to\infty}m_t$. Then $e$ is convex, $e(\alpha)=e(1-\alpha)$, $e(0)=e(1)=0$, $e\le0$ on $[0,1]$ and $e\ge0$ outside it. Moreover,
--   $$e(\alpha)\ge\left(\left|\alpha-\frac12\right|-\frac12\right)\Sigma^+.$$
--   If (E3) holds with finite limit $m$, then $\Sigma^+=m$.
--
--   This records all four clauses, including the absolute value visible on the original PDF page.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 30, Proposition 5.13

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 5.13, PDF p.30. Visual inspection confirms the absolute
value in (5.49); its loss in the extraction is not a source correction.
No E2 assumption occurs in section 5.3; the upper mean may be infinite. -/
theorem proposition_5_13 (D : RegularSystem M)
    (theta : M ≃ᵐ M) (hTRI : IsTimeReversal D.toNonsingularSystem theta)
    (E : AsymptoticES D) :
    ExtendedConvex E.value ∧
    (∀ alpha : ℝ, E.value alpha = E.value (1 - alpha)) ∧
    E.value 0 = 0 ∧ E.value 1 = 0 ∧
    (∀ alpha ∈ Icc (0 : ℝ) 1, E.value alpha ≤ 0) ∧
    (∀ alpha, alpha ∉ Icc (0 : ℝ) 1 → 0 ≤ E.value alpha) ∧
    (∀ alpha : ℝ,
      ((|alpha - 1 / 2| - 1 / 2 : ℝ) : EReal) * upperMean D ≤ E.value alpha) ∧
    (∀ mean : ℝ, Tendsto (scalarMean D) atTop (𝓝 mean) → upperMean D = (mean : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
