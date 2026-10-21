-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_classicalBoundA
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.classicalBoundA
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:52:38.816979+00:00
-- url     : https://prove2.me/theorems/26904497-4f8b-465b-b383-2ae87e659ff1
-- title:
--   Classical lower bound a
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For $n\ge1$,
--   $$m(\mathcal N_n)\ge g(n-1).$$
--   The input ranges over all densities, without a positive Glauber–Sudarshan representation assumption.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 6, §IV.A, lower bound a, Eq.(33)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Eq.(33): classical bound a for n>=1. -/
theorem classicalBoundA (n : ℝ) (hn : 1 ≤ n) :
    ENNReal.ofReal (g (n - 1)) ≤ minimumEntropy (displacementNoiseChannel n) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
