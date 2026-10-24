-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P29_coherentInformationBehavior
-- name    : QAlgorithms.Papers.Independent.Support50.P29.coherentInformationBehavior
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:17:10.20726+00:00
-- url     : https://prove2.me/theorems/32150d96-898f-4e6e-afa4-62ff49ddbb20
-- title:
--   Coherent-information signs, endpoints, and limits
-- statement:
--   For a finite occupation $N\ge0$, let $I_c(N,k)=H(T_k\rho_N)-H(\rho_N,T_k)$, in natural-log units, for the vacuum attenuator/amplifier with amplitude $k\ge0$. Both actual spectral entropies are finite. For every such $k$,
--   $$
--   \begin{aligned}
--   I_c(N,k)<0&\iff N>0\ \text{and}\ k^2<1/2,\\
--   I_c(N,k)=0&\iff N=0\ \text{or}\ k^2=1/2,\\
--   I_c(N,k)>0&\iff N>0\ \text{and}\ k^2>1/2.
--   \end{aligned}
--   $$
--   With $g(N)=(N+1)\log(N+1)-N\log N$ and $g(0)=0$,
--   $$
--   \lim_{k\to0^+}I_c(N,k)=-g(N),\qquad I_c(N,1)=g(N),\qquad
--   \lim_{k\to\infty}I_c(N,k)=0.
--   $$
--   The first limit is taken within the physical domain $k\ge0$. These statements describe the information balance for thermal input, with no claimed numerical rate in the final limit.
-- source:
--   Sending Quantum Information with Gaussian States, arXiv:quant-ph/9809022v1, PDF p. 10, §4, unnumbered: coherent-information signs, endpoints, and limits

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P29

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P29

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma complexify)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity rankOne productCoeff tensorApply IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Frontier30.P10 (WeylSystem)

open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight PureDensity)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (tracePair thermalInput thermalPurificationDensity vacuumChannel exchangeMatrix RealizedDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- Holevo quant-ph/9809022v1, PDF p.10 and Figs.1-2, pp.12-13:
coherent-information signs, endpoints and limits, with no invented convergence
rate. SOURCE CORRECTION: the printed strict signs exclude N=0 (identically
zero) and k=1/sqrt(2) (zero). Both entropies are finite before toReal is used. -/
theorem coherentInformationBehavior (N : ℝ) (hN : 0 ≤ N) :
    (∀ k : ℝ, 0 ≤ k →
      extendedEntropyNats (vacuumChannel k (thermalInput N)) ≠ ⊤ ∧
      extendedEntropyNats (exchangeOutput N k) ≠ ⊤ ∧
      (thermalCoherentInformationNats N k < 0 ↔ 0 < N ∧ k ^ 2 < 1 / 2) ∧
      (thermalCoherentInformationNats N k = 0 ↔ N = 0 ∨ k ^ 2 = 1 / 2) ∧
      (0 < thermalCoherentInformationNats N k ↔ 0 < N ∧ 1 / 2 < k ^ 2)) ∧
    Tendsto (fun k : ℝ => thermalCoherentInformationNats N k) (𝓝[≥] 0)
      (𝓝 (-thermalEntropy N)) ∧
    thermalCoherentInformationNats N 1 = thermalEntropy N ∧
    Tendsto (fun k : ℝ => thermalCoherentInformationNats N k) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P29

end
