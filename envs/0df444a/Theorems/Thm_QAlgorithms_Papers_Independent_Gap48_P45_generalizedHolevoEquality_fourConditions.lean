-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_generalizedHolevoEquality_fourConditions
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.generalizedHolevoEquality_fourConditions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:01:38.406882+00:00
-- url     : https://prove2.me/theorems/9683ee52-2075-44ae-9b7b-e4c2895c9a16
-- title:
--   Proposition 3: generalized Holevo equality, all four equivalent conditions
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $\mu$ be a Borel probability law on the trace-norm state space with $\chi(\mu)=\int D(\rho\|\bar\rho)\,d\mu<\infty$, where $\bar\rho=\int\rho\,d\mu$ is computed from $\mu$. With the explicitly extended Petz channel $\Theta_{\bar\rho}$, the four conditions are equivalent:
--
--   $$\chi(\Phi(\mu))=\chi(\mu)\iff D(\Phi(\rho)\|\Phi(\bar\rho))=D(\rho\|\bar\rho)\ \mu\text{-a.e.}\iff\Theta_{\bar\rho}(\Phi(\rho))=\rho\ \mu\text{-a.e.}\iff\exists\Theta\text{ channel},\ \Theta(\Phi(\rho))=\rho\ \mu\text{-a.e.}$$
--
--   One common recovery channel precedes the almost-everywhere quantifier; no countable domination hypothesis is added.
--
--   This result extends the equality and common-recovery criterion to Borel ensembles.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 20, Proposition 3: generalized Holevo equality, all four equivalent conditions

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

/-- Proposition 3, PDF p.20: all four conditions with computed barycenter and
explicit Petz extension. One recovery precedes almost every state; no countable
mixture dominating the barycenter is assumed. -/
theorem generalizedHolevoEquality_fourConditions
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (mu : GeneralizedEnsemble I)
    (hFinite : ensembleHolevo (id : Matrix I I ℂ → Matrix I I ℂ) mu < ⊤) :
    ((ensembleHolevo Phi.val mu = ensembleHolevo (id : Matrix I I ℂ → Matrix I I ℂ) mu) ↔
      (∀ᵐ rho ∂(mu : Measure (State I)),
        extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val (averageCoefficients mu)) =
          extendedRelativeEntropyNats rho.coefficients (averageCoefficients mu))) ∧
    ((∀ᵐ rho ∂(mu : Measure (State I)),
        extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val (averageCoefficients mu)) =
          extendedRelativeEntropyNats rho.coefficients (averageCoefficients mu)) ↔
      (∀ᵐ rho ∂(mu : Measure (State I)),
        rho.coefficients = petzRecovery Phi.val (averageCoefficients mu) (Phi.val rho.coefficients))) ∧
    ((∀ᵐ rho ∂(mu : Measure (State I)),
        rho.coefficients = petzRecovery Phi.val (averageCoefficients mu) (Phi.val rho.coefficients)) ↔
      ∃ Theta : Channel J I, ∀ᵐ rho ∂(mu : Measure (State I)),
        Theta.val (Phi.val rho.coefficients) = rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
