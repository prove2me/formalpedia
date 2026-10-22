-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_basisSubfamily_explicitRecoveredBasis
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.basisSubfamily_explicitRecoveredBasis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:56:42.466471+00:00
-- url     : https://prove2.me/theorems/f7c4ac8e-00ef-4c71-ba23-2fff085a1661
-- title:
--   Remark 1: explicit recovered orthogonal basis from a basis subfamily
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. In the setting of Corollary 2, suppose $S$ contains the normalized basis family $|v_i\rangle\langle v_i|$, where every vector has a unique convergent ordered expansion in $v_i$. For any strictly positive probability law $\pi$, form $\bar\rho=\sum_i\pi_i|v_i\rangle\langle v_i|$ and $w_i=\sqrt{\pi_i}\bar\rho^{-1/2}v_i$. Then
--
--   $$\{w_i\}\text{ is an orthonormal basis},\qquad \Phi\text{ is reversible on }\{|w_i\rangle\langle w_i|\}.$$
--
--   The inverse images exist and satisfy $\sqrt{\bar\rho}\,w_i=\sqrt{\pi_i}v_i$.
--
--   This result makes the recovered orthogonal family explicit when the source family contains a convergent basis.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 16, Remark 1: explicit recovered orthogonal basis from a basis subfamily

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

/-- Remark 1, PDF pp.16–17: in Corollary 2's reversible setting the computed
whitened basis is an ONB and recovered. Original expansions are ordered. -/
theorem basisSubfamily_explicitRecoveredBasis
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (S : Set (State I)) (hPure : S ⊆ pureStates I)
    (hComplete : CompleteFamily S) (hRev : ReversibleOn Phi.val S)
    (n : ℕ∞) (v : BoundIndex n → Hilbert I)
    (hUnit : ∀ i, ‖v i‖ = 1) (hBasis : UniqueConvergentBasis v)
    (hSubfamily : vectorStates v ⊆ S) (pi : BoundIndex n → ℝ) (hLaw : PositiveLaw pi) :
    (∀ i, positiveSquareRoot (boundedOperator (vectorAverage pi v)) (whitenedVector pi v i) =
      (Real.sqrt (pi i) : ℂ) • v i) ∧ OrthonormalBasisFamily (whitenedVector pi v) ∧
    ReversibleOn Phi.val (vectorStates (whitenedVector pi v)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
