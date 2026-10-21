-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_classicalBoundB
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.classicalBoundB
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:53:15.456359+00:00
-- url     : https://prove2.me/theorems/17d1f41f-b9c6-4908-9d31-e54b72b33030
-- title:
--   Classical lower bound b
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For $n\ge0$,
--   $$m(\mathcal N_n)\ge\ln(2n+1).$$
--   This is the paper's von Neumann lower bound. The companion paper's purity optimization used in its derivation is retained as attributed background.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 6, §IV.A, lower bound b, Eq.(38)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Eq.(38): derived von Neumann bound b. Companion [8]'s purity
maximization remains attributed background, not an original theorem here. -/
theorem classicalBoundB (n : ℝ) (hn : 0 ≤ n) :
    ENNReal.ofReal (Real.log (2 * n + 1)) ≤ minimumEntropy (displacementNoiseChannel n) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
