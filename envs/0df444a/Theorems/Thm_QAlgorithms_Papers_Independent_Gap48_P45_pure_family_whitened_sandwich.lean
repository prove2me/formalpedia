-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_pure_family_whitened_sandwich
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.pure_family_whitened_sandwich
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:02:43.834203+00:00
-- url     : https://prove2.me/theorems/e19422e4-2c16-4557-b650-59c4812b71c8
-- title:
--   Whitened vectors of a complete pure family
-- statement:
--   Let $(\rho_i=|v_i\rangle\langle v_i|)_{i\in L}$ be a complete family of pure states, $(\pi_i)$ a strictly positive probability law, $\sigma=\sum_i\pi_i\rho_i$ and $w_i$ the whitened vectors ($w_i=\sqrt{\pi_i}\,\sigma^{-1/2}v_i$). Then $\sigma^{1/2}w_i=\sqrt{\pi_i}\,v_i$, $(w_i)$ is a Parseval frame, and for every bounded $X$
--
--   $$\sigma^{1/2}X\sigma^{1/2}=\pi_i\,\rho_i\ \Longrightarrow\ X=|w_i\rangle\langle w_i| .$$
--
--   Role: identifies $\Phi^*(B_i)$ with the rank-one projector on the whitened vector in the pure-state clause, once the Petz sandwich identity is known.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, proof of Theorem 3, case r = 1 (PDF pp. 8-9: the vectors sqrt(pi_i) rho-bar^{-1/2} v_i form a Parseval frame and Phi*(B_i) = |w_i><w_i|, equations (8)-(9))

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

theorem pure_family_whitened_sandwich {I L : Type} [Countable I] (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) (v : L → Hilbert I)
    (hv : ∀ i, ‖v i‖ = 1 ∧ (rho i).coefficients = rankOne (v i))
    (pi : L → ℝ) (sigma : State I) (hpi : PositiveLaw pi)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    (∀ i, positiveSquareRoot (boundedOperator (vectorAverage pi v)) (whitenedVector pi v i) =
      (Real.sqrt (pi i) : ℂ) • v i) ∧ IsParsevalFrame (whitenedVector pi v) ∧
    ∀ (i : L) (X : Hilbert I →L[ℂ] Hilbert I),
      (positiveSquareRoot (boundedOperator sigma.coefficients)).comp
          (X.comp (positiveSquareRoot (boundedOperator sigma.coefficients))) =
        (pi i : ℂ) • boundedOperator (rho i).coefficients →
      X = (innerSL ℂ (whitenedVector pi v i)).smulRight (whitenedVector pi v i) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
