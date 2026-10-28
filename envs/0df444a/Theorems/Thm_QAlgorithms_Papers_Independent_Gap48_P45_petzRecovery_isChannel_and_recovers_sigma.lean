-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petzRecovery_isChannel_and_recovers_sigma
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.petzRecovery_isChannel_and_recovers_sigma
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T00:30:42.358483+00:00
-- url     : https://prove2.me/theorems/517b99b2-2efa-487f-bbd3-bdab9f6d021c
-- title:
--   The Petz recovery map is a channel that recovers $\sigma$
-- statement:
--   For a channel $\Phi$ and a state $\sigma$ (possibly degenerate), the computed Petz map $\Theta_\sigma$ is a trace-class channel and
--
--   $$\Theta_\sigma(\Phi(\sigma))=\sigma.$$
--
--   Role: Clause 1 of the parent, and the recovery of $\sigma$ used in both reversibility directions.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, Theorem 1 (PDF pp. 6-7), definition of the Petz channel and Appendix 5.1 (pp. 23-25); D. Petz, Comm. Math. Phys. 105 (1986) 123-131

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

theorem petzRecovery_isChannel_and_recovers_sigma
    {I J : Type} [Countable I] (Phi : Channel I J) (sigma : State I) :
    IsTraceClassChannel (petzRecovery Phi.val sigma.coefficients) ∧
    petzRecovery Phi.val sigma.coefficients (Phi.val sigma.coefficients) = sigma.coefficients := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
