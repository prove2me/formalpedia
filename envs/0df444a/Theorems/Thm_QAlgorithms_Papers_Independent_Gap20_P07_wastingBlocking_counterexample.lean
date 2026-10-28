-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P07_wastingBlocking_counterexample
-- name    : QAlgorithms.Papers.Independent.Gap20.P07.wastingBlocking_counterexample
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:28:12.859745+00:00
-- url     : https://prove2.me/theorems/57a66973-1803-489d-b19e-4ac8b212857c
-- title:
--   Section 7.2: wasting and blocking alone do not suffice
-- statement:
--   There exist positive block lengths $N_\mu$ with $N_{\mu+1}/N_\mu\to\infty$ and positive errors $\epsilon_\mu=\tfrac12\sqrt{N_\mu/N_{\mu+1}}\to0$ such that the finite blocking envelope
--   $$\Delta(n,m)=\min\left\{1,\inf_{\substack{L\text{ finite multiset}\\ m\le\sum_{j\in L}N_j\le n}}\sum_{j\in L}\epsilon_j\right\}$$
--   is monotone under resource wasting and subadditive. The infimum is extended nonnegative; its value for no feasible packing is $+\infty$, before clipping. Along the specified diagonal blocks $\Delta(N_\mu,N_\mu)\to0$, so rate one is sporadically achievable, but the extended supremum of positive rates satisfying the all-sequences definition is zero. Moreover there are positive sequences $n_\nu\to\infty,m_\nu$ for which
--   $$m_\nu/n_\nu\to0,\qquad\liminf_\nu\Delta(n_\nu,m_\nu)\ge\tfrac12.$$
--   This is an abstract error function, not the error of a quantum channel. It shows that wasting and blocking alone do not prove the sporadic-capacity equivalence.
-- source:
--   Tema Con Variazioni: Quantum Channel Capacity, arXiv:quant-ph/0311037v1, PDF p. 27, Section 7.2: wasting and blocking alone do not suffice

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P07

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal Matrix ComplexOrder ComplexConjugate

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap20.P07

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize rankOne tensorApply)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation isometryCoeff conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (stabilizedTraceClassNorm traceClassTensorMap traceClassChannelPower
   transpose transposeBound TraceLinear tracePair MeasurePrepare)

open QAlgorithms.Papers.Independent.Gap48.P29 (fe FiniteCPMap)

/-- PDF p.27, (102)--(103): an abstract clipped blocking envelope, not an error
arising from quantum channels, has sporadic rate one and capacity zero. The
rounding-sensitive bad subsequence is asserted with liminf >=1/2. -/
theorem wastingBlocking_counterexample :
    ∃ (N : ℕ → ℕ+) (epsilon : ℕ → ℝ≥0),
      Tendsto (fun a => (N a : ℕ)) atTop atTop ∧
      Tendsto (fun a => (N (a + 1) : ℝ) / (N a : ℝ)) atTop atTop ∧
      (∀ a, 0 < epsilon a ∧ (epsilon a : ℝ) =
        Real.sqrt ((N a : ℝ) / (N (a + 1) : ℝ)) / 2) ∧
      Tendsto epsilon atTop (𝓝 0) ∧
      ErrorMonotone (blockingEnvelope N epsilon) ∧
      ErrorSubadditive (blockingEnvelope N epsilon) ∧
      Tendsto (fun a => blockingEnvelope N epsilon (N a) (N a)) atTop (𝓝 0) ∧
      Sporadic (blockingEnvelope N epsilon) 1 ∧
      errorCapacity (blockingEnvelope N epsilon) = 0 ∧
      ∃ n m : ℕ → ℕ+, Tendsto (fun a => (n a : ℕ)) atTop atTop ∧
        Tendsto (rateRatio n m) atTop (𝓝 0) ∧
        (1 / 2 : ℝ≥0∞) ≤ Filter.liminf
          (fun a => blockingEnvelope N epsilon (n a) (m a)) atTop := by sorry

end QAlgorithms.Papers.Independent.Gap20.P07

end
