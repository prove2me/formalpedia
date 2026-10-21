-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_5_2
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_5_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:36:05.776546+00:00
-- url     : https://prove2.me/theorems/2e45e29d-c828-4be3-bd7a-bab2aac9cc85
-- title:
--   Zero production and an invariant normal state of finite entropy
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$. Assume also (E2), $\sigma\in L^\infty(\omega)$. Let $m\in\mathbb R$ be the finite limit $m=\lim_{t\to\infty}m_t$ required by (E3).
--
--   Suppose there exist $C,T>0$ such that $|m_t-m|\le C/t$ for every $t\ge T$. If $m=0$, then
--   $$\exists\nu\text{ a probability measure}:\quad (\phi^s)_*\nu=\nu\ (s\in\mathbb R),\quad \nu\ll\omega,\quad\operatorname{Ent}(\nu\mid\omega)>-\infty.$$
--
--   Here $\operatorname{Ent}=-D_{\rm KL}$. The conclusion is a normal countably additive stationary probability, rather than a stationary functional.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 24, Proposition 5.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 5.2, PDF pp.24--25. The O(1/t) constant and threshold
are fixed before t; the conclusion is an invariant normal probability with finite entropy. -/
theorem proposition_5_2 (D : RegularSystem M)
    (hE2 : MemLp (continuousSigma D) ∞ (D.omega : Measure M))
    (mean : ℝ) (hE3 : Tendsto (scalarMean D) atTop (𝓝 mean))
    (hrate : ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → |scalarMean D t - mean| ≤ C / t)
    (hzero : mean = 0) :
    ∃ nu : ProbabilityMeasure M, IsStationary D.toNonsingularSystem nu ∧
      (nu : Measure M) ≪ (D.omega : Measure M) ∧
      (⊥ : EReal) < signedEntropy (nu : Measure M) (D.omega : Measure M) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
