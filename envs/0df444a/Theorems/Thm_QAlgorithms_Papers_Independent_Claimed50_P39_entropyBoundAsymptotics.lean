-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_entropyBoundAsymptotics
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.entropyBoundAsymptotics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T10:55:37.755985+00:00
-- url     : https://prove2.me/theorems/807c3d73-de20-410b-9684-e0e85869bd95
-- title:
--   Relative low- and high-noise sharpness
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   Let $c_1(n)$ be bound c on its $k=1$ branch, and let $d(n)=1+\ln n$. Then
--   $$\lim_{n\downarrow0}\frac{c_1(n)}{g(n)}=1,\qquad\lim_{n\to+\infty}\frac{d(n)}{g(n)}=1.$$
--   The first quotient is taken through strictly positive $n$; this branch is the piecewise bound c throughout a neighborhood of zero.
--
--   These are relative asymptotic equalities, stronger than an additive bounded error.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 6, §IV.A: low/high-noise sharpness

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.6: relative asymptotic sharpness, with the positive punctured
neighborhood at zero. The k=1 branch represents c throughout that neighborhood. -/
theorem entropyBoundAsymptotics :
    Tendsto (fun n : ℝ => boundC 1 n / g n) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) ∧
    Tendsto (fun n : ℝ => (1 + Real.log n) / g n) atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
