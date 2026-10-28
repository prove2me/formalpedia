-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_complete_barycenter_faithful_output
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.complete_barycenter_faithful_output
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:00:10.142541+00:00
-- url     : https://prove2.me/theorems/1fd70559-a6e0-42e0-97dc-bf74c20b6785
-- title:
--   Barycenter of a complete family is faithful and fills the output space
-- statement:
--   Let $\Phi$ be a channel, $(\rho_i)_{i\in L}$ a complete family of states, $(\pi_i)$ a strictly positive probability law and $\sigma=\sum_i\pi_i\rho_i$. Then the projection onto the output space of $\Phi$ equals the support projection of $\Phi(\sigma)$, and $\sigma^{1/2}$ is injective with dense range:
--
--   $$P_{\mathrm{out}}(\Phi)=\operatorname{supp}\Phi(\sigma),\qquad \ker\sigma^{1/2}=0,\quad \overline{\operatorname{ran}}\,\sigma^{1/2}=\mathcal H_I .$$
--
--   Role: identifies the support of $\Phi(\sigma)$ with the output space (so the resolution of the support resolves the output projection) and supplies the injectivity and density used to cancel the sandwich $\sigma^{1/2}X\sigma^{1/2}$.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, proof of Theorem 3 (PDF p. 8: for a complete family the state rho-bar is nondegenerate, so the support of Phi(rho-bar) is the output space of Phi)

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

theorem complete_barycenter_faithful_output {I J L : Type} [Countable I] [Countable J] (Phi : Channel I J) (rho : L → State I)
    (hC : CompleteFamily (Set.range rho)) (pi : L → ℝ) (hpi : PositiveLaw pi) (sigma : State I)
    (hbar : sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) :
    outputProjection Phi.val = coefficientSupportProjection (Phi.val sigma.coefficients) ∧
      Function.Injective (positiveSquareRoot (boundedOperator sigma.coefficients)) ∧
      DenseRange (positiveSquareRoot (boundedOperator sigma.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
