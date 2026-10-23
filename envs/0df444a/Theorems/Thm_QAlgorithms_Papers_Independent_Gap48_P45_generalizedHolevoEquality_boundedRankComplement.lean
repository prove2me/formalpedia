-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_generalizedHolevoEquality_boundedRankComplement
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.generalizedHolevoEquality_boundedRankComplement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:02:27.105747+00:00
-- url     : https://prove2.me/theorems/3c12ba7f-e5c7-45f6-8697-ddcff5247182
-- title:
--   Theorem 5: unambiguous bounded-rank Kraus and r-PEB conclusion
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $r\ge1$ and let $\mu$ be a Borel ensemble of states of rank at most $r$, with full-rank computed average and finite Holevo quantity preserved by $\Phi$. Every fixed complement admits a countable Kraus family and satisfies
--
--   $$\widehat\Phi(X)=\sum_a V_aXV_a^*,\qquad\operatorname{rank}V_a\le r,\qquad\widehat\Phi\text{ is }r\text{-partially entanglement breaking}.$$
--
--   This separately inventoried qualitative conclusion does not claim the deferred numerical bound containing undefined n.
--
--   This result gives the unambiguous complementary-channel obstruction to finite-Holevo equality.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 20, Theorem 5: unambiguous bounded-rank Kraus and r-PEB conclusion

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

/-- Theorem 5's unambiguous bounded-rank conclusion, PDF p.20. The numerical
count with undefined n is separately deferred, not silently repaired. -/
theorem generalizedHolevoEquality_boundedRankComplement
    {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (mu : GeneralizedEnsemble I) (r : ℕ) (hr : 0 < r)
    (hRank : ∀ᵐ rho ∂(mu : Measure (State I)), operatorRank (boundedOperator rho.coefficients) ≤ r)
    (hFullRank : FullRank (averageCoefficients mu))
    (hFinite : ensembleHolevo (id : Matrix I I ℂ → Matrix I I ℂ) mu < ⊤)
    (hEquality : ensembleHolevo Phi.val mu = ensembleHolevo (id : Matrix I I ℂ → Matrix I I ℂ) mu) :
    HasBoundedRankKraus Psi.val r ⊤ ∧ PartiallyEntanglementBreaking Psi.val r := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
