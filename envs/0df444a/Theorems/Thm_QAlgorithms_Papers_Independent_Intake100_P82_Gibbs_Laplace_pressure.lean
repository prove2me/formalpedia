-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_Gibbs_Laplace_pressure
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.Gibbs_Laplace_pressure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:23:44.709855+00:00
-- url     : https://prove2.me/theorems/706cf88c-1fce-48b1-bbfb-587ad0e31ba2
-- title:
--   Lemma 5.4: Laplace pressure identity for weak Gibbs probabilities
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Assume USCE, let $P$ be weak Gibbs for $\mathcal G\in\mathcal A(M)$, and let $\mathcal H=(H_n)\in\mathcal A(M)$ be arbitrary. Then
--   $$\lim_{n\to\infty}\frac1n\log\int e^{H_n}\,dP=p(\mathcal G+\mathcal H)-p(\mathcal G).$$
--   Both pressures are finite and each positive integrand is bounded. No invariance of $P$ or continuity of each $H_n$ is required. This is the AA Laplace-pressure identity.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 35, Lemma 5.4: Laplace pressure identity for weak Gibbs probabilities

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

/-- Lemma 5.4, arXiv:1712.05167v3, PDF p.35. Every AA perturbation,
not just additive continuous tests. The fixed weak Gibbs law may be noninvariant. -/
theorem Gibbs_Laplace_pressure (phi : M → M) (hphi : Continuous phi)
    (hu : USCE phi) (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G)
    (P : ProbabilityMeasure M) (hg : WeakGibbs phi G P)
    (H : ℕ → M → ℝ) (hH : AsymptoticallyAdditive phi H) :
    Tendsto (fun n : ℕ => logSpeed (n + 1)
      (∫⁻ x, ENNReal.ofReal (Real.exp (H (n + 1) x)) ∂(P : Measure M)))
      atTop (𝓝 (separatedSetPressure phi (fun n x => G n x + H n x) - separatedSetPressure phi G)) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
