-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_empirical_upper_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.empirical_upper_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:24:33.842094+00:00
-- url     : https://prove2.me/theorems/bdaba42c-e9dc-49a6-8ea7-09a8b099fef1
-- title:
--   Proposition 5.6: abstract large-deviation upper bound
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   The empirical measure is $\mu_n^x=n^{-1}\sum_{j=0}^{n-1}\delta_{\varphi^j(x)}$. An LDP below is the full speed-$n$ Borel-set principle, with interior in the lower bound and closure in the upper bound. Put
--   $$J_{\mathcal G}(Q)=\begin{cases}p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q),&Q\in\mathcal P_\varphi(M),\\+\infty,&\text{otherwise}.\end{cases}$$
--
--   Assume finite topological entropy and let $\mathcal G\in\mathcal A(M)$ and $P_n\in\mathcal P(M)$. Suppose C1 holds for every continuous $v$, with normalized Laplace limit $p(\mathcal G+Sv)-p(\mathcal G)$. Define $J^*(Q)=\sup_{v\in C(M)}\{\int v\,dQ-p(\mathcal G+Sv)+p(\mathcal G)\}$. For every closed $F\subset\mathcal P(M)$,
--   $$\limsup_{n\to\infty}\frac1n\log P_n\{\mu_n\in F\}\le-\inf_{Q\in F}J^*(Q).$$
--   No S, C2 or USCE is required for this upper bound. The closed set need not consist of invariant probabilities.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 35, Proposition 5.6: abstract large-deviation upper bound

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

/-- Proposition 5.6, arXiv:1712.05167v3, PDF p.35. Every closed subset of
P(M), using the computed dual-pressure rate. No S or C2 is required. -/
theorem empirical_upper_bound (phi : M → M) (hphi : Continuous phi)
    (hfinite : topologicalEntropy phi < ⊤) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (laws : ℕ → ProbabilityMeasure M)
    (hc1 : C1 phi G (fun n => (laws n : Measure M)))
    (F : Set (ProbabilityMeasure M)) (hF : IsClosed F) :
    limsup (fun n : ℕ => logSpeed (n + 1)
      (empiricalEvents phi (fun k => (laws k : Measure M)) (n + 1) F)) atTop ≤
      -(⨅ Q ∈ F, dualRate phi G Q) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
