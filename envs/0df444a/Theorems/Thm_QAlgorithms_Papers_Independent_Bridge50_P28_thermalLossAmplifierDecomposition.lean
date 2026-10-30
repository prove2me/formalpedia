-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P28_thermalLossAmplifierDecomposition
-- name    : QAlgorithms.Papers.Independent.Bridge50.P28.thermalLossAmplifierDecomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:28:07.240276+00:00
-- url     : https://prove2.me/theorems/0687c613-ce3d-4d8e-9def-a81bb11b6ada
-- title:
--   Eq. (2): loss followed by quantum-limited amplification
-- statement:
--   Let $0\le\lambda\le1$ and $N_E\ge0$ be finite real parameters for the full one-mode thermal beam-splitter channel $\mathcal E_{\lambda,N_E}$. Set $G=1+(1-\lambda)N_E$, so $G\ge1$, and $\widetilde\lambda=\lambda/G\in[0,1]$. Let $\mathcal A_G$ be the quantum-limited vacuum amplifier with intensity gain $G$ and amplitude gain $\sqrt G$. Then for every trace-class operator $X$ on the complete Fock space,
--
--   $$
--   \mathcal E_{\lambda,N_E}(X)=\mathcal A_G\bigl(\mathcal E_{\widetilde\lambda,0}(X)\bigr).
--   $$
--
--   This is a channel identity on arbitrary inputs, including non-Gaussian states. The right side performs pure loss before amplification. It includes $G=1$, $\lambda=0$, and $\lambda=1$. The accepted channel constructions use actual Fock/Kraus kernels; no covariance identity is assumed as a replacement for the channel identity.
-- source:
--   The classical capacity of quantum thermal noise channels to within 1.45 bits, arXiv:1207.0256v1, PDF p. 2, Eq. (2): loss followed by quantum-limited amplification

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

/-- Eq.(2), PDF p.2 and explanatory note [19], PDF p.3: loss first, then
quantum-limited amplification. Equality is on EVERY trace-class input, including
non-Gaussian operators, with intensity gain G=1+(1-lambda)NE and amplitude sqrt G.
No covariance identity, channel normalization, or convergence is assumed. -/
theorem thermalLossAmplifierDecomposition
    (lam NE : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hNE : 0 ≤ NE)
    (X : Matrix ℕ ℕ ℂ) (hX : IsTraceClass X) :
    thermalNoiseChannelKernel lam NE X =
      quantumLimitedAmplifierKernel ((1 - lam) * NE + 1)
        (thermalNoiseChannelKernel (lam / ((1 - lam) * NE + 1)) 0 X) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P28

end
