-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_oscillator_channelPeriod
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.oscillator_channelPeriod
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:22:48.921134+00:00
-- url     : https://prove2.me/theorems/2e5fa3b5-7b6d-4cac-bce7-42c03791efdb
-- title:
--   §II remark: harmonic oscillator channel period
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. On the one-mode oscillator let $H|n\rangle=(n+\tfrac12)|n\rangle$ for $n\ge0$, and $\mathcal U_t(\rho)=e^{-itH}\rho e^{itH}$. Then $$\mathcal U_{2\pi}=\mathrm{id}=\mathcal U_0.$$ This is a channel period; the unitary at $2\pi$ is $-I$.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 4, §II remark: harmonic oscillator channel period

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

/-- Section II remark, PDF p.4: oscillator period is a CHANNEL period;
the underlying oscillator unitary at 2pi is minus identity. -/
theorem oscillator_channelPeriod :
    diagonalEvolution (fun n : ℕ => (n : ℝ) + 1 / 2) (2 * Real.pi) = id ∧
    diagonalEvolution (fun n : ℕ => (n : ℝ) + 1 / 2) 0 = id := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
