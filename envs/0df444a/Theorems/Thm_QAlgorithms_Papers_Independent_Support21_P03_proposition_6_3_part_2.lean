-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P03_proposition_6_3_part_2
-- name    : QAlgorithms.Papers.Independent.Support21.P03.proposition_6_3_part_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:42:49.965231+00:00
-- url     : https://prove2.me/theorems/3a5f0f8a-fd4a-4662-9b2e-4827ae0ae060
-- title:
--   Steady entropy LDP with conditional GC rate symmetry
-- statement:
--   Let $(M,\mathcal F,\omega)$ be a probability space and let $\phi^t$ be a group of measurable automorphisms, jointly measurable in time and configuration, with time domain $\mathbb Z$ or $\mathbb R$. Assume that $\omega_t=(\phi^t)_*\omega$ is equivalent to $\omega$ for every time. Set $\ell_t=\log(d\omega_t/d\omega)$ and $c^t=\ell_t\circ\phi^t$. Equalities of observables are modulo $\omega$-null sets. Write $e_t(\alpha)=\log\int e^{\alpha\ell_t}\,d\omega$, retaining extended moment values. A time reversal $\vartheta$ is a measurable involution with $\vartheta\phi^t=\phi^{-t}\vartheta$ and $\vartheta_*\omega=\omega$.
--
--   In continuous time assume (E1): the actual RN densities form a strongly $C^1$ curve in $L^1(\omega)$, and their derivative $\sigma$ at zero has a strongly continuous transported orbit $\sigma_s=\sigma\circ\phi^s$ in $L^1(\omega)$. Write $A_t(x)=\int_0^t\sigma_s(x)\,ds$ and $m_t=t^{-1}\int_0^t\omega(\sigma_s)\,ds$ for $t\ne0$.
--
--   For the NESS assertions assume in addition that $M$ is a complete separable metric space with its Borel sigma algebra, the flow is jointly continuous, and a chosen representative of $\sigma$ is bounded continuous. Assume that the Cesaro family $\{t^{-1}\int_0^t\omega_s\,ds:t\ge1\}$ is precompact for ordinary weak convergence. A selected NESS $\nu$ is a subsequential Cesaro weak limit along times tending to infinity; invariance is not built into this definition.
--
--   Assume time reversal invariance, choose a NESS $\nu$, and suppose $e_+(\alpha)=\lim_{t\to\infty}t^{-1}\log\nu(e^{-\alpha A_t})$ exists and is finite and differentiable for every real $\alpha$. The laws of $A_t/t$ under $\nu$ satisfy the full Borel LDP with
--   $$I_+(s)=\inf_{\alpha\in\mathbb R}\{\alpha s+e_+(\alpha)\}.$$
--   If additionally $e_+(\alpha)=e_+(1-\alpha)$ for every $\alpha$, then $I_+(s)=s+I_+(-s)$.
--
--   Here the full Borel LDP with a nonpositive concave rate $I$ means that $I$ is upper semicontinuous with compact superlevel sets and, for every Borel set $B$, $\sup_{s\in B^\circ}I(s)\le\liminf_{t\to\infty}t^{-1}\log P_t(B)\le\limsup_{t\to\infty}t^{-1}\log P_t(B)\le\sup_{s\in\overline B}I(s)$, with $\log0=-\infty$ and the supremum of the empty set equal to $-\infty$.
--
--   This independent part makes no assertion that all reference Cesaro means converge.
-- source:
--   Entropic Fluctuations in Statistical Mechanics I. Classical Dynamical Systems, arXiv:1009.3248v2, PDF p. 38, Proposition 6.3 part-2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P03

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

section NESS

variable [MetricSpace M] [CompleteSpace M] [TopologicalSpace.SeparableSpace M] [BorelSpace M]

/-- Proposition 6.3 part (2), PDF pp.38--39, independently inventoried.
The complete steady Borel LDP is retained, and GC rate symmetry is conditional.
No full reference Cesaro limit is asserted here. -/
theorem proposition_6_3_part_2 (D : TopologicalSystem M) (hNESS4 : CesaroPrecompact D)
    (theta : M ≃ᵐ M) (hTRI : IsTimeReversal D.toRegularSystem.toNonsingularSystem theta)
    (nu : ProbabilityMeasure M) (hselected : IsSelectedNESS D nu)
    (E : AsymptoticSteadyES D nu)
    (hdiff : ∀ alpha : ℝ, FiniteDifferentiableAt E.value alpha) :
    NegativeRateLDP (steadyMeanLaw D nu) (concaveEntropyRate E.value) ∧
    ((∀ alpha : ℝ, E.value alpha = E.value (1 - alpha)) →
      ∀ s : ℝ, concaveEntropyRate E.value s = (s : EReal) + concaveEntropyRate E.value (-s)) := by sorry

end NESS

end QAlgorithms.Papers.Independent.Support21.P03

end
