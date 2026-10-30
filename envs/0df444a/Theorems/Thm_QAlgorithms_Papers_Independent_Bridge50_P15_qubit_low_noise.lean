-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_qubit_low_noise
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.qubit_low_noise
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:28:07.873239+00:00
-- url     : https://prove2.me/theorems/af9f746a-788a-4675-b5b8-8eb4ff10a0a6
-- title:
--   Closing of the qubit upper/lower gap as noise tends to zero
-- statement:
--   Fix $\eta\in[1/2,1]$. For the qubit channel and extension defined by (7) and (27), let $L_\eta(N)$ be the maximum coherent information of the original channel over diagonal inputs $\rho_p=\operatorname{diag}(1-p,p)$, and let $U_\eta(N)$ be the corresponding diagonal maximum for the extension. Both maxima range over $p\in[0,1]$. For every $N\in[0,1/2]$, they bracket the original capacity: $L_\eta(N)\le Q(\Gamma_{\eta,N})\le U_\eta(N)$, and $U_\eta(0)=L_\eta(0)$. Writing $Q_0=Q(\Gamma_{\eta,0})$, the zero-temperature amplitude-damping capacity in qubits per use, one has
--
--   $$Q_0=L_\eta(0),\qquad \lim_{\substack{N\to0\\0\le N\le1/2}}L_\eta(N)=\lim_{\substack{N\to0\\0\le N\le1/2}}U_\eta(N)=Q_0,$$
--   $$\lim_{\substack{N\to0\\0\le N\le1/2}}\bigl(U_\eta(N)-L_\eta(N)\bigr)=0.$$
--
--   Thus these particular achievable lower and extension upper bounds close at fixed transmissivity. No equality between the noisy original channel's unrestricted single-letter optimization and its diagonal optimization is assumed, and no uniform convergence rate in $\eta$ is asserted.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 5, Closing of the qubit upper/lower gap as noise tends to zero

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

/-- PDF p.5, paragraph after (28): THESE diagonal lower and extension upper
bounds converge to the zero-temperature amplitude-damping capacity, for fixed eta.
The limit is through physical N in [0,1/2], without any uniform rate in eta. -/
theorem qubit_low_noise (eta : ℝ) (heta : eta ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (∀ N ∈ Set.Icc (0 : ℝ) (1 / 2),
      ENNReal.ofReal (qubitLower eta N) ≤ traceClassQuantumCapacity (thermalChannel (1 - eta) N) ∧
      traceClassQuantumCapacity (thermalChannel (1 - eta) N) ≤ ENNReal.ofReal (qubitUpper eta N)) ∧
    qubitUpper eta 0 = qubitLower eta 0 ∧
    traceClassQuantumCapacity (thermalChannel (1 - eta) 0) = ENNReal.ofReal (qubitLower eta 0) ∧
    Tendsto (qubitLower eta) (nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 2)))
      (𝓝 (traceClassQuantumCapacity (thermalChannel (1 - eta) 0)).toReal) ∧
    Tendsto (qubitUpper eta) (nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 2)))
      (𝓝 (traceClassQuantumCapacity (thermalChannel (1 - eta) 0)).toReal) ∧
    Tendsto (fun N => qubitUpper eta N - qubitLower eta N)
      (nhdsWithin 0 (Set.Icc (0 : ℝ) (1 / 2))) (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
