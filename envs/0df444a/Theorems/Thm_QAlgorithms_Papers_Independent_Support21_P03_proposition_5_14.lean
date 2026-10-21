-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_5_14
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_5_14
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:39:25.651546+00:00
-- url     : https://prove2.me/theorems/3d01ac46-bfe2-4ff5-a7ca-cbadd9dd94d4
-- title:
--   Asymptotic mean and the ES large deviation principle
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$.
--
--   Assume time reversal invariance and existence of $e(\alpha)=\lim_{t\to\infty}e_t(\alpha)/t$ for every real $\alpha$. Differentiability of an extended function means finite values in a neighborhood and ordinary real differentiability. If $e$ is differentiable at zero, the finite real mean limit exists and
--   $$\lim_{t\to\infty}m_t=-e'(0).$$
--   If $e$ is differentiable everywhere, the laws $P_t$ of $A_t/t$ satisfy the full Borel LDP with
--   $$I(s)=\inf_{\alpha\in\mathbb R}\{\alpha s+e(\alpha)\},\qquad I(s)=s+I(-s).$$
--
--   Here the full Borel LDP with a nonpositive concave rate $I$ means that $I$ is upper semicontinuous with compact superlevel sets and, for every Borel set $B$, $\sup_{s\in B^\circ}I(s)\le\liminf_{t\to\infty}t^{-1}\log P_t(B)\le\limsup_{t\to\infty}t^{-1}\log P_t(B)\le\sup_{s\in\overline B}I(s)$, with $\log0=-\infty$ and the supremum of the empty set equal to $-\infty$.
--
--   The rate uses the source's nonpositive sign convention.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 30, Proposition 5.14

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

/-- Proposition 5.14, PDF p.30. Part (1) concludes E3 with its actual
finite mean; part (2) keeps the full Borel LDP and rate symmetry.
Bounded entropy production is not assumed in this section. -/
theorem proposition_5_14 (D : RegularSystem M)
    (theta : M ≃ᵐ M) (hTRI : IsTimeReversal D.toNonsingularSystem theta)
    (E : AsymptoticES D) :
    (FiniteDifferentiableAt E.value 0 →
      Tendsto (scalarMean D) atTop (𝓝 (-deriv (fun a => (E.value a).toReal) 0))) ∧
    ((∀ alpha : ℝ, FiniteDifferentiableAt E.value alpha) →
      NegativeRateLDP (continuousMeanLaw D) (concaveEntropyRate E.value) ∧
      ∀ s : ℝ, concaveEntropyRate E.value s = (s : EReal) + concaveEntropyRate E.value (-s)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P03

end
