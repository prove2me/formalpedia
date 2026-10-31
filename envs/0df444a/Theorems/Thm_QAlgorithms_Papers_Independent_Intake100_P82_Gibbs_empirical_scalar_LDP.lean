-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_Gibbs_empirical_scalar_LDP
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.Gibbs_empirical_scalar_LDP
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:20:30.360777+00:00
-- url     : https://prove2.me/theorems/678063b1-ee4a-4cba-8e5b-5f9adc3eef45
-- title:
--   Theorem 4.5: empirical and scalar LDP under weak Gibbs probabilities
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   The empirical measure is $\mu_n^x=n^{-1}\sum_{j=0}^{n-1}\delta_{\varphi^j(x)}$. An LDP below is the full speed-$n$ Borel-set principle, with interior in the lower bound and closure in the upper bound. Put
--   $$J_{\mathcal G}(Q)=\begin{cases}p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q),&Q\in\mathcal P_\varphi(M),\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   Assume USCE and S, and let $P$ be a weak Gibbs probability for $\mathcal G\in\mathcal A(M)$. Under the fixed law $P$ at every time:
--
--   For $\mathcal V=(V_n)\in\mathcal A(M)$, define
--   $$I_{\mathcal V}(s)=\inf_{\substack{Q\in\mathcal P_\varphi(M)\\\mathcal V(Q)=s}}J_{\mathcal G}(Q).$$
--   The empirical measures obey the LDP with lower semicontinuous convex rate $J_{\mathcal G}$. For every such $\mathcal V$, $V_n/n$ obeys the LDP with good convex rate $I_{\mathcal V}$, and
--   $$I_{\mathcal V}(s)=\sup_{\alpha\in\mathbb R}\{\alpha s-p(\mathcal G+\alpha\mathcal V)+p(\mathcal G)\}.$$
--
--   The statement requires neither WPS/PAP nor invariance of the Gibbs law.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 32, Theorem 4.5: empirical and scalar LDP under weak Gibbs probabilities

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

/-- Theorem 4.5, arXiv:1712.05167v3, PDF p.32: all empirical/scalar LDP
conclusions of 3.1. WPS/PAP and invariance of P are not hypotheses. -/
theorem Gibbs_empirical_scalar_LDP (phi : M → M) (hphi : Continuous phi)
    (hu : USCE phi) (hs : Specification phi) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (P : ProbabilityMeasure M) (hg : WeakGibbs phi G P) :
    EmpiricalScalarLDP phi G (fun _ => (P : Measure M)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
