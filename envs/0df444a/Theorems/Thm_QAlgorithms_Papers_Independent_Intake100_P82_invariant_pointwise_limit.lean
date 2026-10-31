-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_invariant_pointwise_limit
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.invariant_pointwise_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:13:11.108009+00:00
-- url     : https://prove2.me/theorems/eed7dfee-06ce-4035-ab77-dafce1b640aa
-- title:
--   Lemma 2.4: pointwise invariant limit of asymptotically additive potentials
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   For every $P\in\mathcal P_\varphi(M)$ and $\mathcal G\in\mathcal A(M)$ there is a bounded Borel function $g$ invariant everywhere under $\varphi$ such that
--   $$\int g\,dP=\mathcal G(P),\qquad G_n(x)/n\longrightarrow g(x)\quad P\text{-a.e.}$$
--   If $P$ is ergodic, then also $g(x)=\mathcal G(P)$ almost everywhere. This is the pointwise invariant representative supplied by the asymptotically additive ergodic theorem.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 20, Lemma 2.4: pointwise invariant limit of asymptotically additive potentials

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

/-- Lemma 2.4, arXiv:1712.05167v3, PDF p.20. A bounded Borel,
everywhere invariant representative, its integral, a.e. convergence and ergodic case. -/
theorem invariant_pointwise_limit (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G)
    (P : ProbabilityMeasure M) (hP : ProbabilityInvariant phi P) :
    ∃ g : M → ℝ, BoundedBorel g ∧ (∀ x, g (phi x) = g x) ∧
      (∫ x, g x ∂(P : Measure M)) = potentialEvaluation G P ∧
      (∀ᵐ x ∂(P : Measure M), Tendsto (fun n : ℕ =>
        G (n + 1) x / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (g x))) ∧
      (Ergodic phi (P : Measure M) → ∀ᵐ x ∂(P : Measure M), g x = potentialEvaluation G P) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
