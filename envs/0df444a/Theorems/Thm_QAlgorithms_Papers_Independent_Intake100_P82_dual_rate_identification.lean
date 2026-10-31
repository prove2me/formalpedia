-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_dual_rate_identification
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.dual_rate_identification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:22:09.238124+00:00
-- url     : https://prove2.me/theorems/e9a2b355-4911-4584-a489-517bd5bd3204
-- title:
--   Lemma 5.1: convex dual rate and entropy formula
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Condition USCE means finite topological entropy and upper semicontinuity of $Q\mapsto h_\varphi(Q)$ on invariant probabilities. S is ordinary specification; WPS is the source weak periodic specification; PAP is finiteness of periodic sets and convergence of their normalized log partition sums to pressure.
--
--   Assume finite topological entropy and let $\mathcal G\in\mathcal A(M)$. Define, rather than independently choose, the pressure dual
--   $$J^*(Q)=\sup_{v\in C(M)}\left\{\int v\,dQ-p(\mathcal G+Sv)+p(\mathcal G)\right\}.$$
--   It is nonnegative, lower semicontinuous and convex on probabilities. If USCE also holds, then $J^*(Q)=p(\mathcal G)-\mathcal G(Q)-h_\varphi(Q)$ on invariant probabilities and $+\infty$ otherwise. This identifies the dual rate without assuming the entropy formula as data.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 33, Lemma 5.1: convex dual rate and entropy formula

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

/-- Lemma 5.1, arXiv:1712.05167v3, PDF p.33. Finite entropy is the domain
needed for real pressure differences; identification additionally assumes USCE. -/
theorem dual_rate_identification (phi : M → M) (hphi : Continuous phi)
    (hfinite : topologicalEntropy phi < ⊤) (G : ℕ → M → ℝ)
    (hG : AsymptoticallyAdditive phi G) :
    IsRate (dualRate phi G) ∧ ProbabilityConvex (dualRate phi G) ∧
      (USCE phi → ∀ Q : ProbabilityMeasure M, dualRate phi G Q = empiricalRate phi G Q) := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
