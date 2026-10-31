-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_Gibbs_C1_C2
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.Gibbs_C1_C2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:24:12.903686+00:00
-- url     : https://prove2.me/theorems/f5378b5a-fc21-4a65-992f-a895e05e46d3
-- title:
--   Lemma 5.5: constant weak Gibbs laws satisfy C1 and C2
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Let $P$ be a weak Gibbs probability for $\mathcal G\in\mathcal A(M)$. Set $P_n=P$ for every positive time. Then both conditions hold:
--
--   For every $v\in C(M)$ assume C1,
--   $$\frac1n\log\int e^{S_nv}\,dP_n\longrightarrow p(\mathcal G+Sv)-p(\mathcal G).$$
--   Assume C2: for every sufficiently small positive $\delta$ there are $n_0(\delta)\ge1$, $K_n(\delta)\ge1$ and integers $0\le m_\delta(n)<n$ on the eventual time domain such that, uniformly in $x$,
--   $$K_n(\delta)^{-1}e^{G_n(x)-np(\mathcal G)}\le P_n(B_{n-m_\delta(n)}(x,\delta)),\quad n\ge n_0(\delta),$$
--   $$\lim_{\delta\downarrow0}\limsup_n\frac{\log K_n(\delta)+m_\delta(n)}n=0.$$
--   The witnesses depend on radius and time, never on the center.
--
--   No S or invariance assumption is used. In C2 the deletion schedule may be chosen identically zero.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 35, Lemma 5.5: constant weak Gibbs laws satisfy C1 and C2

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

/-- Lemma 5.5, arXiv:1712.05167v3, PDF p.35. A constant weak Gibbs law
satisfies C1/C2 with no S or invariance hypothesis. -/
theorem Gibbs_C1_C2 (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G)
    (P : ProbabilityMeasure M) (hg : WeakGibbs phi G P) :
    C1 phi G (fun _ => (P : Measure M)) ∧ C2 phi G (fun _ => (P : Measure M)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
