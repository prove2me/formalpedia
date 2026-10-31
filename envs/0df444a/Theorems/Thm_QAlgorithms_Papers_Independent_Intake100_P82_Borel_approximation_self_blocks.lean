-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_Borel_approximation_self_blocks
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.Borel_approximation_self_blocks
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:26:33.457705+00:00
-- url     : https://prove2.me/theorems/2bb20924-231f-490a-aedd-d113325ae406
-- title:
--   Lemma 6.3: bounded measurable additive approximation implies self-block approximation
-- statement:
--   Let $M$ be a nonempty compact metric space with its Borel sigma-algebra, and let $\varphi:M\to M$ be continuous. Write $\mathcal P(M)$ for Borel probabilities with the weak topology, $\mathcal P_\varphi(M)$ for invariant probabilities, and $\mathcal E_\varphi(M)$ for ergodic probabilities. Entropy $h_\varphi$ is Kolmogorov–Sinai entropy with natural logarithms. For a bounded Borel sequence $\mathcal G=(G_n)_{n\ge1}$, asymptotic additivity means uniform approximation at linear scale by sums $S_n g=\sum_{j=0}^{n-1}g\circ\varphi^j$ of continuous functions. For such a sequence, $\mathcal G(Q)$ denotes the constructed real limit of $n^{-1}\int G_n\,dQ$ on invariant probabilities, and $p(\mathcal G)$ denotes its topological pressure. All time limits use positive integers.
--
--   Let $\mathcal G\subset B(M)$. Suppose bounded Borel functions $f_k$ satisfy $\lim_k\limsup_n n^{-1}\|G_n-S_nf_k\|_\infty=0$. Then
--   $$\lim_{k\to\infty}\limsup_{n\to\infty}\frac1n\|G_n-k^{-1}S_nG_k\|_\infty=0.$$
--   Neither continuity of the approximants nor asymptotic additivity of $\mathcal G$ is assumed. This permits measurable approximation families in Theorem 6.1.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 42, Lemma 6.3: bounded measurable additive approximation implies self-block approximation

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

/-- Lemma 6.3, arXiv:1712.05167v3, PDF p.42. Approximants are bounded Borel;
neither continuity nor asymptotic additivity of G is assumed. -/
theorem Borel_approximation_self_blocks (phi : M → M) (hphi : Continuous phi)
    (G F : ℕ → M → ℝ) (hG : BorelSequence G) (hF : BorelSequence F)
    (ha : AdditiveApproximation phi G F) : SelfBlockApproximation phi G := by sorry

end CompactDynamics

end QAlgorithms.Papers.Independent.Intake100.P82

end
