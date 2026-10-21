-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_thermalBoundA
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.thermalBoundA
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:56:10.543423+00:00
-- url     : https://prove2.me/theorems/817f2c68-5032-437f-94e3-2e99e9f12234
-- title:
--   Thermal lower bound A
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   If $(1-\eta)N\ge\eta$, then
--   $$m(\mathcal E_\eta^N)\ge g((1-\eta)N-\eta).$$
--   The condition ensures that the effective auxiliary mean photon number is physical, including the continuous zero-mean endpoint.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 7, §IV.B, lower bound A, Eq.(48)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.7, Eqs.(48)–(49): thermal bound A on the physical effective-mean domain. -/
theorem thermalBoundA (eta N : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hN : 0 ≤ N) (hphysical : eta ≤ (1 - eta) * N) :
    ENNReal.ofReal (g ((1 - eta) * N - eta)) ≤ minimumEntropy (thermal eta N) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
