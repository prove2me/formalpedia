-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_barycenter_douglas_resolution
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.barycenter_douglas_resolution
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:00:55.963832+00:00
-- url     : https://prove2.me/theorems/d21e10b1-f00d-46d2-9f2d-8d44e10ebfdf
-- title:
--   Douglas resolution of the support of the image of a barycenter
-- statement:
--   Let $\Phi$ be a channel, $(\rho_i)_{i\in L}$ a countable family of states, $(\pi_i)$ a strictly positive probability law and $\sigma=\sum_i\pi_i\rho_i$. Put $t=\Phi(\sigma)^{1/2}$ and let $S$ be the support projection of $\Phi(\sigma)$. Then there are positive operators $B_i$ with $SB_iS=B_i$ and
--
--   $$tB_it=\pi_i\,\Phi(\rho_i),\qquad \sum_i\langle x,B_ix\rangle=\langle x,Sx\rangle\quad(x\in\mathcal H_J).$$
--
--   Role: produces the operators $B_i=\pi_i\Phi(\sigma)^{-1/2}\Phi(\rho_i)\Phi(\sigma)^{-1/2}$ of the proof as a quadratic-form resolution of the support of $\Phi(\sigma)$.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, proof of Theorem 3 (PDF p. 8: the operators pi_i Phi(rho-bar)^{-1/2} Phi(rho_i) Phi(rho-bar)^{-1/2} sum to the projection onto the support of Phi(rho-bar), equation (9)); Douglas factorisation lemma (R. G. Douglas, Proc. AMS 17 (1966) 413-415, Theorem 1)

import Mathlib
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

theorem barycenter_douglas_resolution {I J L : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho : L → State I)
    (pi : L → ℝ) (sigma : State I) (hpi : PositiveLaw pi)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    ∃ B : L → (Hilbert J →L[ℂ] Hilbert J),
      (∀ i, (coefficientSupportProjection (Phi.val sigma.coefficients)).comp
          ((B i).comp (coefficientSupportProjection (Phi.val sigma.coefficients))) = B i) ∧
      (∀ i, (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients))).comp
          ((B i).comp (positiveSquareRoot (boundedOperator (Phi.val sigma.coefficients)))) =
        (pi i : ℂ) • boundedOperator (Phi.val (rho i).coefficients)) ∧
      (∀ i, ContinuousLinearMap.adjoint (B i) = B i ∧ ∀ x, 0 ≤ (inner ℂ x (B i x)).re) ∧
      (∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
        (inner ℂ x (coefficientSupportProjection (Phi.val sigma.coefficients) x)).re) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
