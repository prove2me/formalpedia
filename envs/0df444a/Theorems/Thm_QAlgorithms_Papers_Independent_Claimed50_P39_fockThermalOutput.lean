-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P39_fockThermalOutput
-- name    : QAlgorithms.Papers.Independent.Claimed50.P39.fockThermalOutput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:59:48.638333+00:00
-- url     : https://prove2.me/theorems/61ba644c-b54b-4fe1-b11f-2d4315fd91f1
-- title:
--   Finite binomial formula for thermal Fock outputs
-- statement:
--   Work on the full single-mode Fock Hilbert space $\ell^2(\mathbb N;\mathbb C)$. A density operator is positive and trace class with trace one. Write $\mathcal E_\eta^N$ for the beam-splitter thermal attenuator and $\mathcal N_n$ for the isotropic Gaussian displacement channel, where $0\le\eta\le1$ and $N,n\ge0$ are finite real parameters. Write $S(\rho)\in[0,+\infty]$ for von Neumann entropy in nats, $m(\mathcal C)=\inf_\rho S(\mathcal C(\rho))$, and $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$. No input energy constraint or photon cutoff is imposed unless expressly stated below.
--
--   For any photon number $k\in\mathbb N$, set $p_m=\binom{k}{m}\eta^m(1-\eta)^{k-m}$ for $0\le m\le k$. These are nonnegative and sum to one. Then
--   $$\mathcal E_\eta^0(|k\rangle\langle k|)=\sum_{m=0}^k p_m|m\rangle\langle m|,$$
--   $$\mathcal E_\eta^N(|k\rangle\langle k|)=\sum_{m=0}^k p_m\mathcal N_{(1-\eta)N}(|m\rangle\langle m|).$$
--   The formulas include $k=0$ and both transmissivity endpoints.
--
--   This is a finite convex decomposition of full infinite-dimensional output states.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, PDF p. 10, §VI.A, Eqs.(73)–(75): Fock-state thermal output

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory

open scoped Topology ENNReal

attribute [local instance] Classical.propDecidable

/-- PDF p.10, Eqs.(73)–(75): finite binomial decomposition, including k=0
and both transmissivity endpoints. -/
theorem fockThermalOutput (eta N : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1)
    (hN : 0 ≤ N) (k : ℕ) :
    (∑ m ∈ Finset.range (k + 1), QAlgorithms.Papers.Independent.Information100.P58.binomialWeight k (1 - eta) m) = 1 ∧
    (∀ m ∈ Finset.range (k + 1), 0 ≤ QAlgorithms.Papers.Independent.Information100.P58.binomialWeight k (1 - eta) m) ∧
    thermal eta 0 (B.fockDyad k k) = ∑ m ∈ Finset.range (k + 1),
      (QAlgorithms.Papers.Independent.Information100.P58.binomialWeight k (1 - eta) m : ℂ) • B.fockDyad m m ∧
    thermal eta N (B.fockDyad k k) = ∑ m ∈ Finset.range (k + 1),
      (QAlgorithms.Papers.Independent.Information100.P58.binomialWeight k (1 - eta) m : ℂ) • displacementNoiseChannel ((1 - eta) * N) (B.fockDyad m m) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P39

end
