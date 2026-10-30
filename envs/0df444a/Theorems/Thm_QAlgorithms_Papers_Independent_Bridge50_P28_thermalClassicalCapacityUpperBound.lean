-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P28_thermalClassicalCapacityUpperBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P28.thermalClassicalCapacityUpperBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:28:42.568064+00:00
-- url     : https://prove2.me/theorems/b22262c4-8e78-490a-9486-f074a40d0d3c
-- title:
--   Eq. (3): explicit thermal-channel capacity upper bound
-- statement:
--   Let $0\le\lambda\le1$, $N_E\ge0$, and $N\ge0$ be finite real parameters. Let $\mathcal E_{\lambda,N_E}$ be the full one-mode thermal channel with a fresh independent thermal environment at each use. Its unassisted classical capacity $C_N$ allows arbitrary mixed signals entangled across uses and collective decoding, with vanishing uniform-message average error and uniform-message average input photon expectation at most $nN$ at blocklength $n\ge1$. With $g(x)=(x+1)\ln(x+1)-x\ln x$ and $0\ln0=0$,
--
--   $$
--   C_N(\mathcal E_{\lambda,N_E})\le\frac{g\!\left(\lambda N/\bigl((1-\lambda)N_E+1\bigr)\right)}{\ln2}.
--   $$
--
--   This parameter-dependent bound is sharper than retaining only the uniform additive constant of Theorem 1. The denominator is at least one, and the capacity is an extended operational supremum compared directly with this finite bound.
-- source:
--   The classical capacity of quantum thermal noise channels to within 1.45 bits, arXiv:1207.0256v1, PDF p. 2, Eq. (3): explicit thermal-channel capacity upper bound

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

/-- Eq.(3), PDF p.2: explicit operational thermal-channel upper bound.
The denominator is at least one throughout the physical parameter domain. -/
theorem thermalClassicalCapacityUpperBound
    (lam NE N : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hNE : 0 ≤ NE) (hN : 0 ≤ N) :
    classicalPhotonCapacityBits id (thermalNoiseChannelKernel lam NE) N ≤
      ENNReal.ofReal (thermalUpperBoundBits lam NE N) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P28

end
