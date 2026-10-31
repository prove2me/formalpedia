-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_entropy_density
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.entropy_density
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:11:57.78917+00:00
-- url     : https://prove2.me/theorems/b53708a2-f3a7-40e8-a764-582c47b8b622
-- title:
--   Proposition 2.2: entropy density of ergodic probabilities
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Assume S. For every $P\in\mathcal P_\varphi(M)$ there is a sequence $P_m\in\mathcal E_\varphi(M)$ such that
--   $$P_m\rightharpoonup P,\qquad h_\varphi(P_m)\longrightarrow h_\varphi(P).$$
--   The entropy limit is extended and may be $+\infty$. Neither invertibility, expansiveness nor USCE is required. This is the continuous-map entropy-density extension used by the lower bounds.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 19, Proposition 2.2: entropy density of ergodic probabilities

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

/-- Proposition 2.2, arXiv:1712.05167v3, PDF p.19. Continuous-map version:
neither invertibility nor finite entropy is imposed; entropy may tend to +infinity. -/
theorem entropy_density (phi : M → M) (hphi : Continuous phi)
    (hs : Specification phi) (P : ProbabilityMeasure M) (hP : ProbabilityInvariant phi P) :
    ∃ Q : ℕ → ProbabilityMeasure M,
      (∀ n, Ergodic phi (Q n : Measure M)) ∧
      Tendsto Q atTop (𝓝 P) ∧
      Tendsto (fun n => metricEntropy phi (Q n)) atTop (𝓝 (metricEntropy phi P)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
