-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_thermalBoundsBCD
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.thermalBoundsBCD
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:56:54.952949+00:00
-- url     : https://prove2.me/theorems/8a7eda3e-a030-4daf-a6f1-a258715e8221
-- title:
--   Thermal lower bounds B, C and D
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Put $M=(1-\eta)N\ge0$. Then
--   $$m(\mathcal E_\eta^N)\ge\ln(2M+1).$$
--   For every integer $k\ge1$ such that $(k-1)/2\le M\le k/2$, it also satisfies $m(\mathcal E_\eta^N)\ge c_k(M)$, where $c_k$ and $\lambda_k$ are given by Eqs.(39)–(40). If $M>0$, then $m(\mathcal E_\eta^N)\ge1+\ln M$.
--
--   These are the three classical lower bounds with their complete domains retained after substitution.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 7, §IV.B: lower bounds B, C and D

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.7: thermal bounds B,C,D preserve each classical bound's domain. -/
theorem thermalBoundsBCD (eta N : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (hN : 0 ≤ N) :
    ENNReal.ofReal (Real.log (2 * ((1 - eta) * N) + 1)) ≤ minimumEntropy (thermal eta N) ∧
    (∀ k : ℕ, 1 ≤ k → ((k : ℝ) - 1) / 2 ≤ (1 - eta) * N → (1 - eta) * N ≤ (k : ℝ) / 2 →
      ENNReal.ofReal (boundC k ((1 - eta) * N)) ≤ minimumEntropy (thermal eta N)) ∧
    (0 < (1 - eta) * N → ENNReal.ofReal (1 + Real.log ((1 - eta) * N)) ≤
      minimumEntropy (thermal eta N)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
