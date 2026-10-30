-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_twisted_plob_improvement
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.twisted_plob_improvement
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T14:33:07.481934+00:00
-- url     : https://prove2.me/theorems/51d2e383-2fc7-4d14-96fe-b57453e398a1
-- title:
--   Small-noise and near-EB-threshold improvement over PLOB
-- statement:
--   For the physical non-entanglement-breaking domain $0<\eta<1$, $N\ge0$, $\eta-N(1-\eta)>0$, define
--
--   $$T(\eta,N)=\max\left\{0,\log_2\frac{\eta-N(1-\eta)}{(1+N)(1-\eta)}\right\},$$
--   $$P(\eta,N)=\max\{0,-\log_2(1-\eta)-N\log_2\eta-g(N)\},$$
--
--   where $g(N)=(N+1)\log_2(N+1)-N\log_2N$ and $g(0)=0$. For every fixed $\eta\in(0,1)$ there exists $\delta>0$ such that $T(\eta,N)<P(\eta,N)$ for every $0\le N<\delta$ in that domain. For every fixed $N\ge0$, there exists $\epsilon>0$ such that the same strict comparison holds whenever
--
--   $$\frac{N}{N+1}<\eta<\frac{N}{N+1}+\epsilon,\qquad \eta<1.$$
--
--   These latter inequalities also imply the non-entanglement-breaking condition. Thus the two improvement neighborhoods are parameter-dependent: small noise at fixed transmissivity, or transmissivity just above its admissible lower boundary at fixed noise. No uniform or numerical threshold is asserted.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 7, Small-noise and near-EB-threshold improvement over PLOB

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P15

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology Matrix

namespace QAlgorithms.Papers.Independent.Bridge50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass IsTraceClassChannel productCoeff tensorApply rankOne)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel partialLeft partialRight isometryCoeff WeaklyDegradable GaussianDensity)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Gap48.P26
  (entropyBits PhaseInsensitive weightedPhotonExpectation thermalKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassQuantumCapacity vacuumChannel)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Support50.P07 (qubitPhaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P08 (qubitInput thermalChannel)

/-- PDF p.7 after (40): PLOB improvements in both qualitative regimes.
At fixed N, 'small eta' means approach the non-EB boundary N/(N+1) from above.
Neighborhoods may depend on the fixed parameter; no numerical threshold is supplied. -/
theorem twisted_plob_improvement :
    (∀ eta : ℝ, 0 < eta → eta < 1 → ∃ delta : ℝ, 0 < delta ∧
      ∀ N : ℝ, 0 ≤ N → N < delta → 0 < eta - N * (1 - eta) →
        twistedBound eta N < plobBound eta N) ∧
    (∀ N : ℝ, 0 ≤ N → ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ eta : ℝ, N / (N + 1) < eta → eta < N / (N + 1) + epsilon → eta < 1 →
        0 < eta - N * (1 - eta) ∧ twistedBound eta N < plobBound eta N) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
