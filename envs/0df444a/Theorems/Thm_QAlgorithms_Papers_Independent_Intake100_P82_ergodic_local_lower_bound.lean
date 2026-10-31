-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_ergodic_local_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.ergodic_local_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:24:58.200688+00:00
-- url     : https://prove2.me/theorems/e56f4b1c-967b-4312-8647-4b9e70603190
-- title:
--   Proposition 5.7: ergodic local large-deviation lower bound
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Retain USCE as the surrounding identified-rate context. Let $\mathcal G\in\mathcal A(M)$ and let $P_n$ be arbitrary Borel probabilities.
--
--   Assume C2: for sufficiently small $\delta>0$ there are center-independent $K_n(\delta)\ge1$, $0\le m_\delta(n)<n$ and $n_0(\delta)\ge1$ on the eventual time domain with $P_n(B_{n-m_\delta(n)}(x,\delta))\ge K_n(\delta)^{-1}e^{G_n(x)-np(\mathcal G)}$ for every center, and $\lim_{\delta\downarrow0}\limsup_n (\log K_n(\delta)+m_\delta(n))/n=0$.
--
--   For every open $O\subset\mathcal P(M)$ and every $Q\in O\cap\mathcal E_\varphi(M)$,
--   $$\liminf_n\frac1n\log P_n\{\mu_n\in O\}\ge\mathcal G(Q)+h_\varphi(Q)-p(\mathcal G).$$
--   Here $\mu_n$ is the empirical measure. No C1 or S is assumed. This is the ergodic local lower bound.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 36, Proposition 5.7: ergodic local large-deviation lower bound

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

/-- Proposition 5.7, arXiv:1712.05167v3, PDF p.36. Local lower bound at
every ergodic invariant Q in an open set; numerical bound G(Q)+h(Q)-p(G).
USCE is the surrounding identified-rate context; no C1 or S is assumed. -/
theorem ergodic_local_lower_bound (phi : M → M) (hphi : Continuous phi)
    (hu : USCE phi) (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G)
    (laws : ℕ → ProbabilityMeasure M) (hc2 : C2 phi G (fun n => (laws n : Measure M)))
    (O : Set (ProbabilityMeasure M)) (hO : IsOpen O)
    (Q : ProbabilityMeasure M) (hQO : Q ∈ O) (hQ : Ergodic phi (Q : Measure M)) :
    (potentialEvaluation G Q : EReal) + metricEntropy phi Q - separatedSetPressure phi G ≤
      liminf (fun n : ℕ => logSpeed (n + 1)
        (empiricalEvents phi (fun k => (laws k : Measure M)) (n + 1) O)) atTop := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
