-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_invariant_local_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.invariant_local_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:25:22.042783+00:00
-- url     : https://prove2.me/theorems/c69a59b9-c189-47fb-8a92-34bf0b771810
-- title:
--   Proposition 5.8: invariant local large-deviation lower bound
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Assume USCE and S. Let $\mathcal G\in\mathcal A(M)$ and let $P_n$ be arbitrary Borel probabilities.
--
--   Assume C2: for sufficiently small $\delta>0$ there are center-independent $K_n(\delta)\ge1$, $0\le m_\delta(n)<n$ and $n_0(\delta)\ge1$ on the eventual time domain with $P_n(B_{n-m_\delta(n)}(x,\delta))\ge K_n(\delta)^{-1}e^{G_n(x)-np(\mathcal G)}$ for every center, and $\lim_{\delta\downarrow0}\limsup_n (\log K_n(\delta)+m_\delta(n))/n=0$.
--
--   For every open $O\subset\mathcal P(M)$ and every $Q\in O\cap\mathcal P_\varphi(M)$,
--   $$\liminf_n\frac1n\log P_n\{\mu_n\in O\}\ge\mathcal G(Q)+h_\varphi(Q)-p(\mathcal G).$$
--   Here $\mu_n$ is the empirical measure. The conclusion extends to all invariant $Q$; it does not assume ergodicity of the laws or uniqueness of equilibrium. C1 is not used in this lower-bound step.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 38, Proposition 5.8: invariant local large-deviation lower bound

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

/-- Proposition 5.8, arXiv:1712.05167v3, PDF p.38. S extends the local lower
bound from ergodic Q to every invariant Q. The laws remain arbitrary. -/
theorem invariant_local_lower_bound (phi : M → M) (hphi : Continuous phi)
    (hu : USCE phi) (hs : Specification phi) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) (laws : ℕ → ProbabilityMeasure M)
    (hc2 : C2 phi G (fun n => (laws n : Measure M)))
    (O : Set (ProbabilityMeasure M)) (hO : IsOpen O)
    (Q : ProbabilityMeasure M) (hQO : Q ∈ O) (hQ : ProbabilityInvariant phi Q) :
    (potentialEvaluation G Q : EReal) + metricEntropy phi Q - separatedSetPressure phi G ≤
      liminf (fun n : ℕ => logSpeed (n + 1)
        (empiricalEvents phi (fun k => (laws k : Measure M)) (n + 1) O)) atTop := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
