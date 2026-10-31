-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_asymptotically_additive_extension
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.asymptotically_additive_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:07:31.191415+00:00
-- url     : https://prove2.me/theorems/79a56d0b-a27a-419e-80d4-d7b09541107d
-- title:
--   Unnumbered main result: extension of Theorems A and B to A(M)
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Assume $\varphi$ is an expansive homeomorphism satisfying Bowen specification. Let $\theta$ be a continuous involution with $\varphi^{-1}=\theta\circ\varphi\circ\theta$. No regularity of the potential beyond that stated, uniqueness of equilibrium, or ergodicity is assumed.
--
--   For $M_n=\operatorname{Fix}(\varphi^n)$ finite and nonempty, put $Z_n=\sum_{x\in M_n}e^{G_n(x)}$ and $P_n=Z_n^{-1}\sum_{x\in M_n}e^{G_n(x)}\delta_x$. At the finitely many unused early times with empty periodic sets, use a fixed reference Dirac law. This extension has no effect on any asymptotic assertion.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Choose either C-Commutation, where $\theta$ is an involutive homeomorphism and $\varphi=\theta\circ\varphi\circ\theta$, or R-Reversal, where additionally $\varphi$ is a homeomorphism and $\varphi^{-1}=\theta\circ\varphi\circ\theta$. Set $\theta_n=\theta$ in C and $\theta_n=\theta\circ\varphi^{n-1}$ in R, $\widehat G_n=G_n\circ\theta_n$, $\sigma_n=G_n-\widehat G_n$, and $\operatorname{ep}(Q)=\mathcal G(Q)-\mathcal G(\theta_*Q)$ for invariant $Q$.
--
--   The empirical measure is $\mu_n^x=n^{-1}\sum_{j=0}^{n-1}\delta_{\varphi^j(x)}$. An LDP below is the full speed-$n$ Borel-set principle, with interior in the lower bound and closure in the upper bound. Put
--   $$J_{\mathcal G}(Q)=\begin{cases}p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q),&Q\in\mathcal P_\varphi(M),\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   Let $\mathcal G\in\mathcal A(M)$. Under the periodic laws, the following empirical/scalar LDP conclusions and fluctuation conclusions hold. They also hold under every single fixed weak Gibbs probability for $\mathcal G$.
--
--   For $\mathcal V=(V_n)\in\mathcal A(M)$, define
--   $$I_{\mathcal V}(s)=\inf_{\substack{Q\in\mathcal P_\varphi(M)\\\mathcal V(Q)=s}}J_{\mathcal G}(Q).$$
--   The empirical measures obey the LDP with lower semicontinuous convex rate $J_{\mathcal G}$. For every such $\mathcal V$, $V_n/n$ obeys the LDP with good convex rate $I_{\mathcal V}$, and
--   $$I_{\mathcal V}(s)=\sup_{\alpha\in\mathbb R}\{\alpha s-p(\mathcal G+\alpha\mathcal V)+p(\mathcal G)\}.$$
--
--   The empirical rate satisfies $J_{\mathcal G}(\theta_*Q)=J_{\mathcal G}(Q)+\operatorname{ep}(Q)$ for every invariant $Q$. Moreover $\sigma_n/n$ obeys the full LDP with good convex rate
--   $$I(s)=\inf_{\substack{Q\in\mathcal P_\varphi(M)\\\operatorname{ep}(Q)=s}}J_{\mathcal G}(Q),\qquad I(-s)=I(s)+s.$$
--   Writing $e(\alpha)=p((1-\alpha)\mathcal G+\alpha\widehat{\mathcal G})-p(\mathcal G)$, one also has $I(s)=\sup_\alpha\{\alpha s-e(-\alpha)\}$.
--
--   This extends both introductory principles to bounded Borel asymptotically additive potentials.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 9, Unnumbered main result: extension of Theorems A and B to A(M)

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

/-- Unnumbered AA extension of A/B, arXiv:1712.05167v3, PDF p.9.
The general nonadditive rate identity is restricted to invariant probabilities.
Both periodic and fixed weak Gibbs laws are included. -/
theorem asymptotically_additive_extension (f theta : M ≃ₜ M)
    (h : IntroHypotheses f theta) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive f G) (reference : M) :
    (EmpiricalScalarLDP f G (periodicLaw f G reference) ∧
      FluctuationPrinciple f G theta true (periodicLaw f G reference)) ∧
    ∀ P : ProbabilityMeasure M, WeakGibbs f G P →
      EmpiricalScalarLDP f G (fun _ => (P : Measure M)) ∧
      FluctuationPrinciple f G theta true (fun _ => (P : Measure M)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
