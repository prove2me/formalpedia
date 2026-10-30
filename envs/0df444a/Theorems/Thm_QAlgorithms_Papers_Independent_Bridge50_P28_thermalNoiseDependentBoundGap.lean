-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P28_thermalNoiseDependentBoundGap
-- name    : QAlgorithms.Papers.Independent.Bridge50.P28.thermalNoiseDependentBoundGap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:29:33.651114+00:00
-- url     : https://prove2.me/theorems/400384a1-6ce7-4c84-afb2-56ea8c2450e4
-- title:
--   Unnumbered refinement after Theorem 1: noise-dependent gap
-- statement:
--   For finite real parameters $0\le\lambda\le1$, $N_E\ge0$, and $N\ge0$, put $Y=(1-\lambda)N_E$. Let $g(x)=(x+1)\ln(x+1)-x\ln x$, with $0\ln0=0$. Define the numerical bounds $U=g(\lambda N/(Y+1))/\ln2$ and $\gamma=[g(\lambda N+Y)-g(Y)]/\ln2$. For $Y>0$,
--
--   $$
--   U-\gamma\le\frac{Y\ln(1+Y^{-1})}{\ln2}.
--   $$
--
--   For the noise-free boundary $Y=0$, $U-\gamma=0$. The formulas also allow $N=0$ or $\lambda=0$, when the difference vanishes.
--
--   The refined quantity bounds the difference between the displayed upper and lower bounds. Together with Eq.(3) it controls the unknown capacity gap; it is not an asserted exact expression for that gap.
-- source:
--   The classical capacity of quantum thermal noise channels to within 1.45 bits, arXiv:1207.0256v1, PDF p. 2, Unnumbered refinement after Theorem 1: noise-dependent gap

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P28

open Filter

open scoped BigOperators NNReal ENNReal Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassChannelPower tracePair)

open QAlgorithms.Papers.Independent.Gap48.P26 (weightedPhotonExpectation)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Unnumbered refinement after Theorem 1, PDF p.2: difference of the two
NUMERICAL bounds, not an equality for unknown capacity. The inverse-noise
formula is asserted only for positive noise; zero noise has exactly zero gap. -/
theorem thermalNoiseDependentBoundGap
    (lam NE N : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hNE : 0 ≤ NE) (hN : 0 ≤ N) :
    (0 < (1 - lam) * NE →
      thermalUpperBoundBits lam NE N - coherentSignalRateBits lam NE N ≤
        ((1 - lam) * NE * Real.log (1 + ((1 - lam) * NE)⁻¹)) / Real.log 2) ∧
    ((1 - lam) * NE = 0 →
      thermalUpperBoundBits lam NE N - coherentSignalRateBits lam NE N = 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P28

end
