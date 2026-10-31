-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_theorem_B
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.theorem_B
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:06:56.786789+00:00
-- url     : https://prove2.me/theorems/5951b807-b74d-41f8-8163-dbc56ce9ceb7
-- title:
--   Theorem B: additive Gibbs Fluctuation Principle
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Assume $\varphi$ is an expansive homeomorphism satisfying Bowen specification. Let $\theta$ be a continuous involution with $\varphi^{-1}=\theta\circ\varphi\circ\theta$. No regularity of the potential beyond that stated, uniqueness of equilibrium, or ergodicity is assumed.
--
--   The empirical measure is $\mu_n^x=n^{-1}\sum_{j=0}^{n-1}\delta_{\varphi^j(x)}$. An LDP below is the full speed-$n$ Borel-set principle, with interior in the lower bound and closure in the upper bound. Put
--   $$J_{\mathcal G}(Q)=\begin{cases}p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q),&Q\in\mathcal P_\varphi(M),\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   Let $g\in C(M)$ and let $P$ be any weak Gibbs probability for $(S_n g)$. Set $\sigma=g-g\circ\theta$ and $J=J_{(S_ng)}$. Under the single law $P$ at every time, $\mu_n$ and $S_n\sigma/n$ obey the LDP with rates $J$ and
--   $$I(s)=\inf_{Q\in\mathcal P(M):\,\int\sigma\,dQ=s}J(Q).$$
--   These same rates satisfy $J(\theta_*Q)=J(Q)+\int\sigma\,dQ$ for every $Q$ and $I(-s)=I(s)+s$ for every real $s$. No invariance of $P$ or convergence from periodic laws is required. This is the Gibbs fluctuation principle.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 5, Theorem B: additive Gibbs Fluctuation Principle

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

/-- Theorem B, arXiv:1712.05167v3, PDF p.5: the same rates as Theorem A,
under one fixed weak Gibbs law, which need not be invariant. -/
theorem theorem_B (f theta : M ≃ₜ M) (h : IntroHypotheses f theta)
    (g : C(M, ℝ)) (P : ProbabilityMeasure M) (hP : WeakGibbs f (orbitSum f g) P) :
    AdditiveFluctuationPrinciple f g theta (fun _ => (P : Measure M)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
