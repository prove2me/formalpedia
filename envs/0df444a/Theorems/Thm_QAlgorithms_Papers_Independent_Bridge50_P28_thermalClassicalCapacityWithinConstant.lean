-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P28_thermalClassicalCapacityWithinConstant
-- name    : QAlgorithms.Papers.Independent.Bridge50.P28.thermalClassicalCapacityWithinConstant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:26:51.081312+00:00
-- url     : https://prove2.me/theorems/82cd8a5b-805e-415c-9565-fc0e39625b85
-- title:
--   Theorem 1: thermal classical capacity within 1/ln 2 bits
-- statement:
--   Let $0\le\lambda\le1$, $N_E\ge0$, and $N\ge0$ be finite real parameters. On the complete one-mode Fock space, let $\mathcal E_{\lambda,N_E}$ mix the input with an independent thermal environment of mean photon number $N_E$ at an intensity-$\lambda$ beam splitter. Let $C_N$ be its unassisted classical capacity in bits per use, allowing arbitrary mixed and entangled block inputs and collective decoding. Energy is the photon expectation of the uniform-message average block input, at most $nN$ for each positive blocklength $n$; average decoding error tends to zero. With natural logarithms, define $g(x)=(x+1)\ln(x+1)-x\ln x$, with $0\ln0=0$, and $\gamma=[g(\lambda N+(1-\lambda)N_E)-g((1-\lambda)N_E)]/\ln2$. Then
--
--   $$
--   \gamma\le C_N(\mathcal E_{\lambda,N_E})\le\gamma+\frac1{\ln2}.
--   $$
--
--   This bounds the possible advantage over the coherent-signal rate by a universal additive constant. The lower bound is credited by the paper to Holevo; both inequalities are part of its stated theorem.
--
--   **Formalization Note** Capacity is the extended nonnegative supremum of operationally achievable rates, independently defined from codes. Finite real bounds are embedded into that extended domain; infinity cannot disappear through a real conversion.
-- source:
--   The classical capacity of quantum thermal noise channels to within 1.45 bits, arXiv:1207.0256v1, PDF p. 2, Theorem 1: thermal classical capacity within 1/ln 2 bits

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

/-- Theorem 1, PDF p.2 (abstract on p.1): both capacity inequalities over
all physical parameters, including noiseless, vacuum-input, and transmissivity
endpoints. Capacity permits arbitrary entangled block inputs and decoding.
Holevo's lower inequality is cited background included by the source theorem. -/
theorem thermalClassicalCapacityWithinConstant
    (lam NE N : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hNE : 0 ≤ NE) (hN : 0 ≤ N) :
    ENNReal.ofReal (coherentSignalRateBits lam NE N) ≤
      classicalPhotonCapacityBits id (thermalNoiseChannelKernel lam NE) N ∧
    classicalPhotonCapacityBits id (thermalNoiseChannelKernel lam NE) N ≤
      ENNReal.ofReal (coherentSignalRateBits lam NE N + 1 / Real.log 2) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P28

end
