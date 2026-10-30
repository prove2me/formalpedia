-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_twisted_bound_dominance
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.twisted_bound_dominance
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T14:32:15.708792+00:00
-- url     : https://prove2.me/theorems/d569e67f-55c0-425c-bde8-84736b5a6d0f
-- title:
--   Pointwise improvement over the extended and SWAT bounds
-- statement:
--   Let $0<\eta<1$, $N\ge0$, and $\eta-N(1-\eta)>0$. Define
--
--   $$T=\max\left\{0,\log_2\frac{\eta-N(1-\eta)}{(1+N)(1-\eta)}\right\},\quad E=\max\left\{0,\log_2\frac\eta{1-\eta}+g(N)\right\},$$
--   $$S=\max\left\{0,\log_2\frac\eta{1-\eta}-\log_2(N+1)\right\},\quad g(N)=(N+1)\log_2(N+1)-N\log_2N.$$
--
--   Then $T\le E$ and $T\le S$, with $g(0)=0$. These are the scalar twisted, extension-expression, and SWAT bounds in bits. Equality is allowed at zero noise and after clipping. This pointwise comparison does not assert that the extension expression equals an extension capacity outside its separately established weak-degradability regime.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 7, Pointwise improvement over the extended and SWAT bounds

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

/-- PDF p.7 after (40): 'better' means no larger, with equality permitted
at N=0 and when clipping gives zero. Scalar comparison, without extending the
extension-capacity identity to eta<1/2. -/
theorem twisted_bound_dominance (eta N : ℝ) (heta : 0 < eta) (heta1 : eta < 1)
    (hN : 0 ≤ N) (hprime : 0 < eta - N * (1 - eta)) :
    twistedBound eta N ≤ extendedBound eta N ∧ twistedBound eta N ≤ swatBound eta N := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
