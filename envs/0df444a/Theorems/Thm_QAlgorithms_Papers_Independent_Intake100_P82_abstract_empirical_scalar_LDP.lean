-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_abstract_empirical_scalar_LDP
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.abstract_empirical_scalar_LDP
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:22:43.469371+00:00
-- url     : https://prove2.me/theorems/4c5613a7-41e6-4879-81b5-ba4e9eed6d1c
-- title:
--   Theorem 5.2: abstract empirical and asymptotically additive LDP
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   The empirical measure is $\mu_n^x=n^{-1}\sum_{j=0}^{n-1}\delta_{\varphi^j(x)}$. An LDP below is the full speed-$n$ Borel-set principle, with interior in the lower bound and closure in the upper bound. Put
--   $$J_{\mathcal G}(Q)=\begin{cases}p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q),&Q\in\mathcal P_\varphi(M),\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   Assume S and USCE. Let $P_n$ be any sequence of Borel probabilities and let $\mathcal G\in\mathcal A(M)$.
--
--   For every $v\in C(M)$ assume C1,
--   $$\frac1n\log\int e^{S_nv}\,dP_n\longrightarrow p(\mathcal G+Sv)-p(\mathcal G).$$
--   Assume C2: for every sufficiently small positive $\delta$ there are $n_0(\delta)\ge1$, $K_n(\delta)\ge1$ and integers $0\le m_\delta(n)<n$ on the eventual time domain such that, uniformly in $x$,
--   $$K_n(\delta)^{-1}e^{G_n(x)-np(\mathcal G)}\le P_n(B_{n-m_\delta(n)}(x,\delta)),\quad n\ge n_0(\delta),$$
--   $$\lim_{\delta\downarrow0}\limsup_n\frac{\log K_n(\delta)+m_\delta(n)}n=0.$$
--   The witnesses depend on radius and time, never on the center.
--
--   For $\mathcal V=(V_n)\in\mathcal A(M)$, define
--   $$I_{\mathcal V}(s)=\inf_{\substack{Q\in\mathcal P_\varphi(M)\\\mathcal V(Q)=s}}J_{\mathcal G}(Q).$$
--   The empirical measures obey the LDP with lower semicontinuous convex rate $J_{\mathcal G}$. For every such $\mathcal V$, $V_n/n$ obeys the LDP with good convex rate $I_{\mathcal V}$, and
--   $$I_{\mathcal V}(s)=\sup_{\alpha\in\mathbb R}\{\alpha s-p(\mathcal G+\alpha\mathcal V)+p(\mathcal G)\}.$$
--
--   This is the complete abstract empirical and asymptotically additive LDP criterion.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 33, Theorem 5.2: abstract empirical and asymptotically additive LDP

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

/-- Theorem 5.2, arXiv:1712.05167v3, PDF pp.33--34. Arbitrary law sequence;
C1/C2 are the actual Laplace and shortened-ball bounds, not assumed LDP data. -/
theorem abstract_empirical_scalar_LDP (phi : M → M) (hphi : Continuous phi)
    (hu : USCE phi) (hs : Specification phi) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (laws : ℕ → ProbabilityMeasure M)
    (hc1 : C1 phi G (fun n => (laws n : Measure M)))
    (hc2 : C2 phi G (fun n => (laws n : Measure M))) :
    EmpiricalScalarLDP phi G (fun n => (laws n : Measure M)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
