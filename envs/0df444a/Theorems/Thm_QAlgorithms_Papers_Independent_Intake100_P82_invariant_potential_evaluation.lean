-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_invariant_potential_evaluation
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.invariant_potential_evaluation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:12:20.967824+00:00
-- url     : https://prove2.me/theorems/945da8bf-0505-455f-801c-7fe7f1c00c92
-- title:
--   Lemma 2.3: uniform invariant-potential evaluation
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   For $\mathcal G\in\mathcal A(M)$, the constructed value $\mathcal G(P)$ is finite for every invariant $P$. For every continuous approximating family $g_k$,
--   $$\frac1n\int G_n\,dP\longrightarrow\mathcal G(P),\qquad\int g_k\,dP\longrightarrow\mathcal G(P).$$
--   Both convergences are uniform over all invariant probabilities, and $P\mapsto\mathcal G(P)$ is continuous in the weak topology. The value is computed from $\mathcal G$, not chosen independently. This makes asymptotic potential evaluation usable in contraction formulas.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 19, Lemma 2.3: uniform invariant-potential evaluation

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

/-- Lemma 2.3, arXiv:1712.05167v3, PDF p.19. Constructed real evaluation,
both uniform limits, and weak continuity, for every continuous approximating family. -/
theorem invariant_potential_evaluation (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G) :
    (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, ∀ P : InvariantProbability phi,
      |(∫ x, G (n + 1) x ∂(P.val : Measure M)) / ((n + 1 : ℕ) : ℝ) -
        potentialEvaluation G P.val| < e) ∧
    (∀ F : ℕ → M → ℝ, ApproximatingFamily phi G F →
      ∀ e : ℝ, 0 < e → ∃ K : ℕ, ∀ k ≥ K, ∀ P : InvariantProbability phi,
        |(∫ x, F (k + 1) x ∂(P.val : Measure M)) - potentialEvaluation G P.val| < e) ∧
    Continuous (fun P : InvariantProbability phi => potentialEvaluation G P.val) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
