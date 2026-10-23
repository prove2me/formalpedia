-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_whiteningBasis_orthonormalBasis
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.whiteningBasis_orthonormalBasis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:10:22.520739+00:00
-- url     : https://prove2.me/theorems/a198629e-e9aa-4e4a-bb39-0fe846b271a4
-- title:
--   Lemma 8: whitening a nonorthogonal basis gives an orthonormal basis
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $\{v_i\}$ be a normalized finite or countable basis of $H$ in the sense of unique convergent ordered expansions. For any strictly positive probability distribution $\pi_i$, compute $\bar\rho=\sum_i\pi_i|v_i\rangle\langle v_i|$. The inverse-square-root images exist and
--
--   $$w_i=\sqrt{\pi_i}\bar\rho^{-1/2}v_i,\qquad\sqrt{\bar\rho}\,w_i=\sqrt{\pi_i}v_i,\qquad\{w_i\}\text{ is an orthonormal basis}.$$
--
--   This result constructs the orthogonal family used in the reversibility normal form.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 25, Lemma 8: whitening a nonorthogonal basis gives an orthonormal basis

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

/-- Lemma 8, PDF pp.25–26 with (9), p.8: whitening a normalized unique
convergent-expansion basis gives an ONB for every positive law. The p.26 proof
says apply rho_bar; its displayed equation instead uses sqrt(rho_bar).
The statement keeps inverse exponent -1/2 and explicitly supplies the domain equation. -/
theorem whiteningBasis_orthonormalBasis
    {I : Type} [Countable I] [Nonempty I]
    (n : ℕ∞) (v : BoundIndex n → Hilbert I)
    (hUnit : ∀ i, ‖v i‖ = 1) (hBasis : UniqueConvergentBasis v)
    (pi : BoundIndex n → ℝ) (hLaw : PositiveLaw pi) :
    (∀ i, positiveSquareRoot (boundedOperator (vectorAverage pi v)) (whitenedVector pi v i) =
      (Real.sqrt (pi i) : ℂ) • v i) ∧ OrthonormalBasisFamily (whitenedVector pi v) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
