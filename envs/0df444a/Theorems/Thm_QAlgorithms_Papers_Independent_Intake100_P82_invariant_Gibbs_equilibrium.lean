-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_invariant_Gibbs_equilibrium
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.invariant_Gibbs_equilibrium
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:20:02.748461+00:00
-- url     : https://prove2.me/theorems/cc05e56a-bcfb-4af0-95f9-790ab62ab89f
-- title:
--   Lemma 4.4: invariant weak Gibbs probabilities are equilibrium
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   If $\mathcal G\in\mathcal A(M)$ and $P$ is an invariant weak Gibbs probability for it, then $P$ is equilibrium:
--   $$p(\mathcal G)=\mathcal G(P)+h_\varphi(P).$$
--   No ergodicity, uniqueness or converse is asserted. The invariance condition is essential for this conclusion.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 32, Lemma 4.4: invariant weak Gibbs probabilities are equilibrium

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

/-- Lemma 4.4, arXiv:1712.05167v3, PDF p.32. Invariant weak Gibbs
probabilities are equilibrium states; no converse, uniqueness or ergodicity. -/
theorem invariant_Gibbs_equilibrium (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : AsymptoticallyAdditive phi G)
    (P : ProbabilityMeasure M) (hP : ProbabilityInvariant phi P) (hg : WeakGibbs phi G P) :
    Equilibrium phi G P := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
