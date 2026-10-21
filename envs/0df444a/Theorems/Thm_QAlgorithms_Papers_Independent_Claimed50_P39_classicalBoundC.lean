-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_classicalBoundC
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.classicalBoundC
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:53:46.522266+00:00
-- url     : https://prove2.me/theorems/cc1b9b19-4ff7-439a-93a2-e004978776c8
-- title:
--   Classical lower bound c
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For an integer $k\ge1$ and $(k-1)/2\le n\le k/2$, define
--   $$\lambda_k(n)=\frac{1-\sqrt{1-(k+1)(1-k/(2n+1))}}{k+1},\quad c_k(n)=-\lambda_k(n)\ln\lambda_k(n)-(1-\lambda_k(n))\ln\frac{1-\lambda_k(n)}k.$$
--   Then
--   $$m(\mathcal N_n)\ge c_k(n).$$
--   The square root uses its nonnegative branch and zero logarithmic products use their continuous value. The adjacent endpoint values are $\ln k$ and $\ln(k+1)$.
--
--   This retains the piecewise sharp entropy envelope rather than only its purity corollary.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 6, §IV.A, lower bound c, Eqs.(39)–(40), Appendix C

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Eqs.(39)–(40): bound c with the source's closed interval. -/
theorem classicalBoundC (k : ℕ) (hk : 1 ≤ k) (n : ℝ)
    (hn0 : ((k : ℝ) - 1) / 2 ≤ n) (hn1 : n ≤ (k : ℝ) / 2) :
    ENNReal.ofReal (boundC k n) ≤ minimumEntropy (displacementNoiseChannel n) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
