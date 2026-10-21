-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_corollary_5_5
-- name    : QAlgorithms.Papers.Independent.Support21.P03.corollary_5_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:38:17.048985+00:00
-- url     : https://prove2.me/theorems/e2558b2a-7cef-4f00-801b-8f74f2cba913
-- title:
--   A common almost-sure mean and a normal stationary state force zero production
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$. Assume also (E2), $\sigma\in L^\infty(\omega)$. Let $m\in\mathbb R$ be the finite limit $m=\lim_{t\to\infty}m_t$ required by (E3).
--
--   Suppose there is an invariant probability absolutely continuous with respect to $\omega$. If for some nondecreasing sequence $t_n\to+\infty$,
--   $$\frac1{t_n}\int_0^{t_n}\sigma_s(x)\,ds\longrightarrow m\quad\text{for }\omega\text{-almost every }x,$$
--   then $m=0$.
--
--   Regularity by exponential summability is not required of this sequence.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 25, Corollary 5.5

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Corollary 5.5, PDF p.25: the witnessing sequence need not be regular. -/
theorem corollary_5_5 (D : RegularSystem M)
    (hE2 : MemLp (continuousSigma D) ∞ (D.omega : Measure M))
    (mean : ℝ) (hE3 : Tendsto (scalarMean D) atTop (𝓝 mean))
    (hnormal : ∃ nu : ProbabilityMeasure M, IsStationary D.toNonsingularSystem nu ∧
      (nu : Measure M) ≪ (D.omega : Measure M))
    (hpointwise : ∃ tn : ℕ → ℝ, Monotone tn ∧ Tendsto tn atTop atTop ∧
      ∀ᵐ x ∂(D.omega : Measure M),
        Tendsto (fun n => pointMean D (tn n) x) atTop (𝓝 mean)) :
    mean = 0 := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
