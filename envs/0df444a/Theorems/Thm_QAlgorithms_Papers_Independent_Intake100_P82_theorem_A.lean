-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_theorem_A
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.theorem_A
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:06:35.044973+00:00
-- url     : https://prove2.me/theorems/1b70ddc4-c5e1-4983-a5c2-20b9d858548d
-- title:
--   Theorem A: additive Periodic Orbits Fluctuation Principle (seed pinned from abstract)
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Assume $\varphi$ is an expansive homeomorphism satisfying Bowen specification. Let $\theta$ be a continuous involution with $\varphi^{-1}=\theta\circ\varphi\circ\theta$. No regularity of the potential beyond that stated, uniqueness of equilibrium, or ergodicity is assumed.
--
--   For $M_n=\operatorname{Fix}(\varphi^n)$ finite and nonempty, put $Z_n=\sum_{x\in M_n}e^{S_n g(x)}$ and $P_n=Z_n^{-1}\sum_{x\in M_n}e^{S_n g(x)}\delta_x$. At the finitely many unused early times with empty periodic sets, use a fixed reference Dirac law. This extension has no effect on any asymptotic assertion.
--
--   The empirical measure is $\mu_n^x=n^{-1}\sum_{j=0}^{n-1}\delta_{\varphi^j(x)}$. An LDP below is the full speed-$n$ Borel-set principle, with interior in the lower bound and closure in the upper bound. Put
--   $$J_{\mathcal G}(Q)=\begin{cases}p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q),&Q\in\mathcal P_\varphi(M),\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   Let $g\in C(M)$ and $\sigma=g-g\circ\theta$, and take $\mathcal G=(S_n g)$. Under $P_n$, both $\mu_n$ and $S_n\sigma/n$ satisfy the LDP, with respective rates $J=J_{\mathcal G}$ and
--   $$I(s)=\inf_{\substack{Q\in\mathcal P(M)\\\int\sigma\,dQ=s}}J(Q).$$
--   For every probability $Q$ and every real $s$,
--   $$J(\theta_*Q)=J(Q)+\int\sigma\,dQ,\qquad I(-s)=I(s)+s.$$
--   This is the additive periodic-orbits fluctuation principle.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 4, Theorem A: additive Periodic Orbits Fluctuation Principle (seed pinned from abstract)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

section CompactDynamics

variable {M : Type*} [instMetric : MetricSpace M] [instCompact : CompactSpace M]
  [instNonempty : Nonempty M] [instMeasurable : MeasurableSpace M] [instBorel : BorelSpace M]

-- Retain standing assumptions even when a displayed lemma does not use them.

include instCompact instNonempty instBorel

local instance : DecidableEq M := Classical.decEq M

/-- Theorem A, arXiv:1712.05167v3, PDF p.4: empirical LDP, scalar contraction,
and both rate fluctuation identities, for every continuous potential. -/
theorem theorem_A (f theta : M ≃ₜ M) (h : IntroHypotheses f theta)
    (g : C(M, ℝ)) (reference : M) :
    AdditiveFluctuationPrinciple f g theta (periodicLaw f (orbitSum f g) reference) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
