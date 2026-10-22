-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_pureFamilyRecovery_orthogonalFamilyAndDimension
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.pureFamilyRecovery_orthogonalFamilyAndDimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:56:00.226388+00:00
-- url     : https://prove2.me/theorems/d700fcd1-b63b-4c69-ae3d-69cdec313f68
-- title:
--   Corollary 2: recovery of some orthogonal complete family and dimension inequality
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $\Phi$ be reversible on a complete family $S$ of pure states. There is an orthonormal basis $\{v_i\}$, not required to lie in $S$, whose pure states are all recovered by one channel, and
--
--   $$\Phi\text{ is reversible on }\{|v_i\rangle\langle v_i|\},\qquad \dim H_A\le\dim H_B.$$
--
--   This result extracts a recoverable orthogonal basis and an obstruction from output dimension.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 16, Corollary 2: recovery of some orthogonal complete family and dimension inequality

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

/-- Corollary 2, PDF p.16: recovered orthogonal family AND dimension inequality. -/
theorem pureFamilyRecovery_orthogonalFamilyAndDimension
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (S : Set (State I)) (hPure : S ⊆ pureStates I)
    (hComplete : CompleteFamily S) (hRev : ReversibleOn Phi.val S) :
    (∃ (L : Type) (_ : Countable L) (v : L → Hilbert I),
      OrthonormalBasisFamily v ∧ ReversibleOn Phi.val (vectorStates v)) ∧
    dimensionCount I ≤ dimensionCount J := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
