-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_beamArrayEntropy
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.beamArrayEntropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:03:05.982737+00:00
-- url     : https://prove2.me/theorems/173bb74d-3876-4096-bd59-9b9749a5ff9f
-- title:
--   Beam-array entropy inequalities
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For an integer $k\ge2$, $N,n\ge0$, and any mixed or pure density $\rho$,
--   $$kS\!\left(\mathcal E_{1/k}^{N+nk/(k-1)}(\rho)\right)\ge S(\mathcal N_n(\rho))+(k-1)g(n+N).$$
--   For every norm-one $u$ the pure-input specialization at zero added noise gives
--   $$kS(\mathcal E_{1/k}^N(|u\rangle\langle u|))\ge(k-1)g(N).$$
--   At reservoir mean $N=0$ the mixed-input inequality gives
--   $$kS\!\left(\mathcal E_{1/k}^{nk/(k-1)}(\rho)\right)\ge S(\mathcal N_n(\rho))+(k-1)g(n).$$
--   All arithmetic permits infinite entropy and uses no subtraction.
--
--   These are the entropy estimates D1,D7,D8; intermediate network representations are proof objects rather than extra hypotheses.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 14, Appendix D, Eqs.(D1), (D5)–(D8)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- Appendix D, PDF pp.13–14, D1,D7,D8: beam-array entropy estimates.
D7 holds for arbitrary mixed inputs; k>=2 and all reservoirs are nonnegative.
Extended nonnegative arithmetic permits infinite entropy without subtraction. -/
theorem beamArrayEntropy (k : ℕ) (hk : 2 ≤ k) (N n : ℝ) (hN : 0 ≤ N) (hn : 0 ≤ n)
    (X : B.FockOperator) (hX : B.IsDensity X) :
    fockEntropyNats (displacementNoiseChannel n X) + ENNReal.ofReal (((k : ℝ) - 1) * g (n + N)) ≤
      (k : ℝ≥0∞) * fockEntropyNats (thermal (1 / (k : ℝ)) (N + n * k / ((k : ℝ) - 1)) X) ∧
    (∀ u : B.Fock, ‖u‖ = 1 →
      ENNReal.ofReal (((k : ℝ) - 1) * g N) ≤
        (k : ℝ≥0∞) * fockEntropyNats (thermal (1 / (k : ℝ)) N (pureState u))) ∧
    fockEntropyNats (displacementNoiseChannel n X) + ENNReal.ofReal (((k : ℝ) - 1) * g n) ≤
      (k : ℝ≥0∞) * fockEntropyNats (thermal (1 / (k : ℝ)) (n * k / ((k : ℝ) - 1)) X) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
