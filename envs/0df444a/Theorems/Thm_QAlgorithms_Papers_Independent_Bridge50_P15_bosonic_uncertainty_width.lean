-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_bosonic_uncertainty_width
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.bosonic_uncertainty_width
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:30:30.977384+00:00
-- url     : https://prove2.me/theorems/f25a8f9c-3a6b-48f4-b814-ee58cfed6f6f
-- title:
--   Explicit uncertainty width 2g(N) and its small-noise limit
-- statement:
--   Fix $1/2\le\eta<1$ and let $N\ge0$. Define $a_\eta=\log_2(\eta/(1-\eta))$, $g(N)=(N+1)\log_2(N+1)-N\log_2N$ with $g(0)=0$, and the finite scalar endpoints $L_\eta(N)=\max\{0,a_\eta-g(N)\}$ and $U_\eta(N)=\max\{0,a_\eta+g(N)\}$. For the unconstrained, unassisted quantum capacity of the full-Fock thermal attenuator,
--
--   $$L_\eta(N)\le Q(\mathcal E_{\eta,N})\le U_\eta(N),\qquad 0\le U_\eta(N)-L_\eta(N)\le2g(N).$$
--   $$\lim_{N\to0^+}2g(N)=\lim_{N\to0^+}\bigl(U_\eta(N)-L_\eta(N)\bigr)=0.$$
--
--   All quantities and rates use bits. The width compares finite endpoints, so it does not subtract extended capacities. Clipping can make the width strictly smaller than $2g(N)$; for example, at $\eta=1/2$ it equals $g(N)$. This quantifies the source's small-noise uncertainty claim.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 6, Explicit uncertainty width 2g(N) and its small-noise limit

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

/-- PDF p.6 following (33), comparing p.4 (18): finite endpoint width at most
2g(N), with small-noise convergence. Clipping prevents an equality in general. -/
theorem bosonic_uncertainty_width (eta N : ℝ) (heta : (1 / 2 : ℝ) ≤ eta)
    (heta1 : eta < 1) (hN : 0 ≤ N) :
    ENNReal.ofReal (gaussianLower eta N) ≤ traceClassQuantumCapacity (bosonicChannel eta N) ∧
    traceClassQuantumCapacity (bosonicChannel eta N) ≤ ENNReal.ofReal (extendedBound eta N) ∧
    0 ≤ extendedBound eta N - gaussianLower eta N ∧
    extendedBound eta N - gaussianLower eta N ≤ 2 * thermalEntropyBits N ∧
    Tendsto (fun t => 2 * thermalEntropyBits t) (nhdsWithin 0 (Set.Ici (0 : ℝ))) (𝓝 0) ∧
    Tendsto (fun t => extendedBound eta t - gaussianLower eta t)
      (nhdsWithin 0 (Set.Ici (0 : ℝ))) (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
