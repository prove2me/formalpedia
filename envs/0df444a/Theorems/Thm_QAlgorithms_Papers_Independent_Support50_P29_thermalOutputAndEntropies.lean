-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P29_thermalOutputAndEntropies
-- name    : QAlgorithms.Papers.Independent.Support50.P29.thermalOutputAndEntropies
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:13:50.707795+00:00
-- url     : https://prove2.me/theorems/f52173ee-5064-4acc-af5b-18ba0a5fd44c
-- title:
--   Thermal output and the three entropies
-- statement:
--   Let $\hbar>0$, $N\ge0$ be a finite mean photon number, and $k\ge0$ the amplitude coefficient. On the full one-mode Fock space let $\rho_N$ be the normalized thermal state with characteristic function $\exp[-\hbar(N+1/2)|z|^2/2]$, and let $T_k$ be the quantum-limited attenuator or amplifier with a fixed vacuum environment. Define
--   $$
--   \widetilde N=\begin{cases}k^2N,&k\le1,\\k^2N+k^2-1,&k>1.\end{cases}
--   $$
--   Then $T_k(\rho_N)=\rho_{\widetilde N}$. For $g(x)=(x+1)\log(x+1)-x\log x$, with $0\log0=0$, the actual von Neumann entropies in nats are finite and satisfy
--   $$
--   H(\rho_N)=g(N),\qquad H(T_k(\rho_N))=g(\widetilde N),\qquad
--   H(\rho_N,T_k)=\begin{cases}g((1-k^2)N),&k\le1,\\g((k^2-1)(N+1)),&k>1.\end{cases}
--   $$
--   Entropy exchange is the spectral entropy of $(T_k\otimes\mathrm{Id})(\rho_{12})$ for the normalized pure Schmidt purification, whose system marginal is $\rho_N$. The identity endpoint uses the convention stated on p.10. These formulas evaluate the three sides of the information triangle; they assert no capacity optimization.
-- source:
--   Sending Quantum Information with Gaussian States, arXiv:quant-ph/9809022v1, PDF p. 9, §4, unnumbered main result: thermal output and all three entropies

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

/-- Holevo quant-ph/9809022v1, PDF pp.8-9, §4: the actual thermal output
and all three entropies in nats, in both channel regimes. The input exponent
uses hbar/2 as in (3.9), correcting the repeated hbar/4 misprint on p.9;
the amplifier is specified by (4.11), with the physical creation-mode noise. -/
theorem thermalOutputAndEntropies (N k hbar : ℝ)
    (hN : 0 ≤ N) (hk : 0 ≤ k) (hhbar : 0 < hbar) :
    RealizedDensity (thermalInput N) ∧
    RealizedDensity (vacuumChannel k (thermalInput N)) ∧
    PureDensity (thermalPurificationDensity N) ∧
    partialRight (thermalPurificationDensity N) = thermalInput N ∧
    RealizedDensity (exchangeOutput N k) ∧
    (∀ z : ℂ, QAlgorithms.Papers.Independent.Claimed50.P35.oneModeCharacteristic
      hbar (thermalInput N) z =
      Complex.exp (((-hbar * (N + 1 / 2) * Complex.normSq z / 2 : ℝ) : ℂ))) ∧
    vacuumChannel k (thermalInput N) = thermalInput (outputNumber N k) ∧
    extendedEntropyNats (thermalInput N) = ENNReal.ofReal (thermalEntropy N) ∧
    extendedEntropyNats (vacuumChannel k (thermalInput N)) =
      ENNReal.ofReal (thermalEntropy (outputNumber N k)) ∧
    extendedEntropyNats (exchangeOutput N k) = ENNReal.ofReal
      (thermalEntropy (if k ≤ 1 then (1 - k ^ 2) * N else (k ^ 2 - 1) * (N + 1))) := by sorry

end QAlgorithms.Papers.Independent.Support50.P29

end
