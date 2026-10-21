-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_noiseMonotonicity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.noiseMonotonicity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:49:24.175928+00:00
-- url     : https://prove2.me/theorems/8195c94c-8508-40cb-8a43-223e7a08112d
-- title:
--   Pointwise entropy monotonicity in noise
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For every density $\rho$ and every added noise $\Delta\ge0$,
--   $$S(\mathcal N_{n+\Delta}(\rho))\ge S(\mathcal N_n(\rho)),\qquad S(\mathcal E_\eta^{N+\Delta}(\rho))\ge S(\mathcal E_\eta^N(\rho)).$$
--   The comparison is nondecreasing and pointwise in the input. It imposes no pointwise entropy monotonicity in transmissivity.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 4, Eqs.(21)–(22): entropy monotonicity in noise

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.4, Eqs.(21)–(22): pointwise nondecreasing entropy with added noise. -/
theorem noiseMonotonicity (eta N n delta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hN : 0 ≤ N) (hn : 0 ≤ n) (hd : 0 ≤ delta)
    (X : B.FockOperator) (hX : B.IsDensity X) :
    fockEntropyNats (displacementNoiseChannel n X) ≤ fockEntropyNats (displacementNoiseChannel (n + delta) X) ∧
    fockEntropyNats (thermal eta N X) ≤ fockEntropyNats (thermal eta (N + delta) X) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
