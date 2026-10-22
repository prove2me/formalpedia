-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_boundedRankReversibility_complement
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.boundedRankReversibility_complement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:44:40.58899+00:00
-- url     : https://prove2.me/theorems/176d3efb-cdf1-47a5-a515-c415ea105976
-- title:
--   Theorem 3 (seed paper result): bounded-rank reversibility and the pure-state normal form
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Write $H_B^\Phi$ for the closed span of all output supports, $d_\Phi=\dim H_B^\Phi$, $m_0(\Phi)=\dim\ker(\Phi^*|_{\mathcal B(H_B^\Phi)})$, and $m_r=\min\{m_0(\Phi)+r^2,d_\Phi\}$; dimensions retain infinity. Let $S=\{\rho_i\}_{i\in L}$ be a complete finite or countable family with $\operatorname{rank}\rho_i\le r$, where $r\ge1$. If one channel recovers every member after $\Phi$, every fixed complement $\widehat\Phi$ admits a countable Kraus family $V_a$ satisfying
--
--   $$\#\{a\}\le |L|m_r,\qquad \operatorname{rank}V_a\le r.$$
--
--   The complement is $r$-partially entanglement breaking; every ancillary output is in fact a countable convex mixture of normalized pure states of Schmidt rank at most $r$. If $r=1$, write $\rho_i=|v_i\rangle\langle v_i|$ with $\|v_i\|=1$. For every strictly positive probability law $\pi_i$, compute $\bar\rho=\sum_i\pi_i|v_i\rangle\langle v_i|$ and $w_i=\sqrt{\pi_i}\bar\rho^{-1/2}v_i$. These inverse images exist, $\{w_i\}$ is Parseval, and there are mutually orthogonal vectors $\psi_{ik}$ within each row with $\sum_k\|\psi_{ik}\|^2=1$ such that
--
--   $$\widehat\Phi(X)=\sum_i\langle w_i|X|w_i\rangle\sum_{k=1}^{m_1}|\psi_{ik}\rangle\langle\psi_{ik}|.$$
--
--   This result provides a necessary structural condition on the complementary channel and its exact pure-family normal form.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 8, Theorem 3 (seed paper result): bounded-rank reversibility and the pure-state normal form

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

/-- Theorem 3, PDF p.8, both clauses. Complementarity uses the SAME isometry.
Input count and dimensions retain infinity. No probability law is a hypothesis
of the rank assertion; every positive law is allowed for the pure assertion. -/
theorem boundedRankReversibility_complement
    {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (rho : L → State I) (r : ℕ) (hr : 0 < r)
    (hComplete : CompleteFamily (Set.range rho))
    (hRank : ∀ i, operatorRank (boundedOperator (rho i).coefficients) ≤ r)
    (hRev : ReversibleOn Phi.val (Set.range rho)) :
    HasBoundedRankKraus Psi.val r (dimensionCount L * rankMultiplicity Phi.val r) ∧
    PartiallyEntanglementBreaking Psi.val r ∧ CountableSchmidtOutputs Psi.val r ∧
    (r = 1 → ∀ (v : L → Hilbert I), (∀ i, ‖v i‖ = 1 ∧ (rho i).coefficients = rankOne (v i)) →
      ∀ pi : L → ℝ, PositiveLaw pi → HasWhitenedForm Psi.val pi v (rankMultiplicity Phi.val 1)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
