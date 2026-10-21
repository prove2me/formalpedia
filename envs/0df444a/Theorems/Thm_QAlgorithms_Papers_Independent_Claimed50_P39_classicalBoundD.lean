-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_classicalBoundD
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.classicalBoundD
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:54:23.450061+00:00
-- url     : https://prove2.me/theorems/a280d20a-6fb7-4181-8497-f580c0f04e1c
-- title:
--   Classical lower bound d
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For every $n>0$,
--   $$m(\mathcal N_n)\ge1+\ln n.$$
--   The singular zero-noise logarithm is excluded. The inequality is valid even when its real lower bound is negative; nonnegative entropy then also gives the stronger trivial lower bound zero.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 6, §IV.A, lower bound d, Eqs.(41), (47)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF pp.6–7, Eqs.(41),(47): bound d for every strictly positive noise. -/
theorem classicalBoundD (n : ℝ) (hn : 0 < n) :
    ENNReal.ofReal (1 + Real.log n) ≤ minimumEntropy (displacementNoiseChannel n) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
