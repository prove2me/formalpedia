-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_thermalBoundF
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.thermalBoundF
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:57:53.98663+00:00
-- url     : https://prove2.me/theorems/819ae2ec-1537-44f3-a636-ae90dc0182af
-- title:
--   Thermal lower bound F
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For any integer $k\ge1$, put $M=(1-\eta)N$. Then
--   $$m(\mathcal E_\eta^N)\ge\frac{k-1}k g(M)+\frac1k m(\mathcal N_M)\quad(\eta\le1/k).$$
--   If $\eta\ge1/k$ and $t=M-\eta+1/k\ge0$, then
--   $$m(\mathcal E_\eta^N)\ge\frac{k-1}k g(t)+\frac1k m(\mathcal N_t).$$
--   If $\eta\le1/k$ and the classical minimum-entropy conjecture holds at $M$, then the first displayed inequality is equality. The only conjectural hypothesis is the single-use classical lower bound at that actual noise; no additivity is assumed. The classical term is its actual unrestricted infimum, not a selected numerical bound. For $k=1$ the first branch is precisely Eq.(26).
--
--   This preserves the conditional strength available from later information about the classical minimum.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 7, §IV.B, lower bound F, Eq.(51)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.7, Eq.(51): bound F with the true classical minimum. k=1 gives
Eq.(26), and the second branch requires a physical nonnegative noise parameter.
The first branch is equality under the classical entropy conjecture at its actual
noise M=(1-eta)N, as stated immediately after Eq.(51); no additivity is assumed. -/
theorem thermalBoundF (eta N : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hN : 0 ≤ N) (k : ℕ) (hk : 1 ≤ k) :
    (eta ≤ 1 / (k : ℝ) →
      ENNReal.ofReal (((k : ℝ) - 1) / k * g ((1 - eta) * N)) +
        ENNReal.ofReal (1 / (k : ℝ)) * minimumEntropy (displacementNoiseChannel ((1 - eta) * N)) ≤
          minimumEntropy (thermal eta N)) ∧
    (1 / (k : ℝ) ≤ eta → 0 ≤ (1 - eta) * N - eta + 1 / (k : ℝ) →
      ENNReal.ofReal (((k : ℝ) - 1) / k * g ((1 - eta) * N - eta + 1 / (k : ℝ))) +
        ENNReal.ofReal (1 / (k : ℝ)) *
          minimumEntropy (displacementNoiseChannel ((1 - eta) * N - eta + 1 / (k : ℝ))) ≤
            minimumEntropy (thermal eta N)) ∧
    (eta ≤ 1 / (k : ℝ) → ClassicalEntropyConjecture ((1 - eta) * N) →
      ENNReal.ofReal (((k : ℝ) - 1) / k * g ((1 - eta) * N)) +
        ENNReal.ofReal (1 / (k : ℝ)) * minimumEntropy (displacementNoiseChannel ((1 - eta) * N)) =
          minimumEntropy (thermal eta N)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
