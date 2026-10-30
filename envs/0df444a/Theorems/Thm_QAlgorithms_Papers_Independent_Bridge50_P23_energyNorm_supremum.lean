-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_energyNorm_supremum
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.energyNorm_supremum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:26:15.740815+00:00
-- url     : https://prove2.me/theorems/747ea0a1-d495-41de-9a5e-7c62d38535be
-- title:
--   Lemma 4(3)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. For every source superoperator $\Delta$, $$\sup_{E>0}\|\Delta\|_{\diamond E}=\|\Delta\|_\diamond.$$ The supremum is over all positive budgets, so removing the energy restriction recovers the unrestricted stabilized trace norm.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 5, Lemma 4(3)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P23

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P23

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsTraceClass traceSize tensorApply rankOne productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel traceSecond traceFirst homogeneousEntropy generalizedRelativeEntropy
   channelTensorAction finiteInputCoherentInfo)

open QAlgorithms.Papers.Independent.Frontier18.P08 (IsQuantumOperation)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable closedFormExpectation GibbsCondition TensorBlockIndex blockAction blockEnergy)

open QAlgorithms.Papers.Independent.Claimed50.P18 (finiteFirstConditionalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 4(3), PDF p.5: the increasing supremum over every positive budget
is the unrestricted diamond norm. No real default-valued supremum is used. -/
theorem energyNorm_supremum {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (H : PositiveObservable I) (hH : Grounded H)
    (D : Matrix I I ℂ → Matrix J J ℂ) (hD : IsSuperoperator D) :
    (⨆ E : {E : ℝ // 0 < E}, energyMagnitude H E.val D) = diamondMagnitude D := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
