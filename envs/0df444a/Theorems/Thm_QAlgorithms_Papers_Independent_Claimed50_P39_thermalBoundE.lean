-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_thermalBoundE
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.thermalBoundE
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:57:20.586256+00:00
-- url     : https://prove2.me/theorems/48a608d2-a7ce-438d-b653-a487ee0cac9d
-- title:
--   Thermal lower bound E
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For any integer $k\ge2$, write $M=(1-\eta)N$. Then
--   $$m(\mathcal E_\eta^N)\ge\frac{k-1}k g\!\left(\frac{k}{k-1}M\right)\quad(\eta\le1/k).$$
--   If $\eta\ge1/k$ and $t=M-\eta+1/k\ge0$, then
--   $$m(\mathcal E_\eta^N)\ge\frac{k-1}k g\!\left(\frac{k}{k-1}t\right).$$
--   The integer and auxiliary-noise guards are the physical Appendix D domain. Both branches agree at $\eta=1/k$.
--
--   This records the beam-splitter lower bound without totalizing its singular $k=1$ formula.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 7, §IV.B, lower bound E, Eq.(50)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.7, Eq.(50): bound E, k>=2 and nonnegative auxiliary reservoir.
These are the physical domains used by Appendix D, not negative g arguments. -/
theorem thermalBoundE (eta N : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hN : 0 ≤ N) (k : ℕ) (hk : 2 ≤ k) :
    (eta ≤ 1 / (k : ℝ) → ENNReal.ofReal
      (((k : ℝ) - 1) / k * g ((k : ℝ) / ((k : ℝ) - 1) * ((1 - eta) * N))) ≤
        minimumEntropy (thermal eta N)) ∧
    (1 / (k : ℝ) ≤ eta → 0 ≤ (1 - eta) * N - eta + 1 / (k : ℝ) →
      ENNReal.ofReal (((k : ℝ) - 1) / k * g ((k : ℝ) / ((k : ℝ) - 1) *
        ((1 - eta) * N - eta + 1 / (k : ℝ)))) ≤ minimumEntropy (thermal eta N)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
