-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_weak_almost_additive_self_blocks
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.weak_almost_additive_self_blocks
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:26:12.824991+00:00
-- url     : https://prove2.me/theorems/2042ab2c-f246-4c97-b542-e6b3bb5febb2
-- title:
--   Lemma 6.2: weak almost additivity implies self-block approximation
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Let $\mathcal G\subset B(M)$ be weakly almost additive: $|G_{m+n}-G_m-G_n\circ\varphi^m|\le C_m$ for positive $m,n$, with $C_m/m\to0$. Then
--   $$\lim_{k\to\infty}\limsup_{n\to\infty}\frac1n\|G_n-k^{-1}S_nG_k\|_\infty=0.$$
--   The error depends on the left block, rather than being one fixed constant. No continuity of the terms is assumed. This is the self-block approximation used in the characterizations.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 41, Lemma 6.2: weak almost additivity implies self-block approximation

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

/-- Lemma 6.2, arXiv:1712.05167v3, PDF p.41. Weak almost additivity with
left-block-dependent sublinear error implies the self-block approximation. -/
theorem weak_almost_additive_self_blocks (phi : M → M) (hphi : Continuous phi)
    (G : ℕ → M → ℝ) (hG : BorelSequence G) (hw : WeakAlmostAdditive phi G) :
    SelfBlockApproximation phi G := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
