-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_barycenter_dominates_and_inherits_reversibility
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.barycenter_dominates_and_inherits_reversibility
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T10:59:14.055054+00:00
-- url     : https://prove2.me/theorems/7f0e63ef-3060-4b21-850f-d24c7d2fef09
-- title:
--   Barycenter of a reversible family: domination and inherited reversibility
-- statement:
--   Let $\Phi$ be a channel, $(\rho_i)_{i\in L}$ a countable family of states and $(\pi_i)$ a strictly positive probability law. Then the coefficient barycenter
--
--   $$\bar\rho=\sum_i\pi_i\rho_i$$
--
--   is a state, every member has finite (Lindblad) relative entropy to it, $D(\rho_i\|\bar\rho)<\infty$ (indeed $\le 1-\log\pi_i$ since $\bar\rho\ge\pi_i\rho_i$), and if $\Phi$ is reversible on $\{\rho_i\}$ then it is reversible on each pair $\{\rho_i,\bar\rho\}$.
--
--   Role: supplies the reference state $\sigma=\bar\rho$ and the finiteness hypothesis needed to apply the Petz criterion (petz_threeConditions, clause 3) to every member of the family in the parent's proof.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, proof of Theorem 3 (PDF p. 8, the barycenter rho-bar of equation (9)); operator monotonicity of log for the bound D(rho||sigma) <= -log c when sigma >= c rho (standard, e.g. Ohya-Petz, Quantum Entropy and Its Use, Ch. 1)

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

theorem barycenter_dominates_and_inherits_reversibility
    {I J L : Type} [Countable I] [Countable J] [Countable L] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (rho : L → State I) (pi : L → ℝ) (hpi : PositiveLaw pi) :
    ∃ sigma : State I,
      (sigma.coefficients = fun a b => ∑' i, (pi i : ℂ) * (rho i).coefficients a b) ∧
      (∀ i, extendedRelativeEntropyNats (rho i).coefficients sigma.coefficients < ⊤) ∧
      (ReversibleOn Phi.val (Set.range rho) → ∀ i, ReversibleOn Phi.val {rho i, sigma}) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
