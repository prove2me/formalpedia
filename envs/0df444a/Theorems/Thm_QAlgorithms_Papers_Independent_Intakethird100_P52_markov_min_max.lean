-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_markov_min_max
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.markov_min_max
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:56:56.146462+00:00
-- url     : https://prove2.me/theorems/74c51f67-7f7d-473e-8b47-95881b8dcec4
-- title:
--   Corollary 19: min/max conditional information and short quantum Markov chains
-- statement:
--   All Hilbert spaces below are finite dimensional and nonzero over $\mathbb C$. A density operator is positive semidefinite with trace one. Every spectral power is zero on the kernel, including zero and negative powers. Information quantities use base-two logarithms, with $\log_2 0=-\infty$; the operator logarithms in exponential formulas are natural logarithms.
--
--   Let $\rho=\rho_{ABC}$ be a tripartite density operator. Its marginals $\rho_{AC},\rho_{BC},\rho_C$ are computed by partial trace from this same state. Operators on fewer registers are extended by identities. Use tensor order $A\otimes(C\otimes B)$, and set $\sigma=\rho_{AC}\otimes I_B$ and $\mathcal N=\operatorname{Tr}_A$. Define $I_a(A;B\mid C)_\rho=\Delta_a(\rho,\sigma,\mathcal N)$ and $\widetilde I_a(A;B\mid C)_\rho=\widetilde\Delta_a(\rho,\sigma,\mathcal N)$. A short quantum Markov chain $A-C-B$ means that the whole space $H_C$ decomposes as $\bigoplus_j H_{C_{L,j}}\otimes H_{C_{R,j}}$ and $\rho=\bigoplus_j q_j\rho_{AC_{L,j}}\otimes\rho_{C_{R,j}B}$, where $q_j\ge0$, $\sum_jq_j=1$, and both factors in each block are density operators.
--
--   The Petz map and min/max divergences are
--   $$
--   \mathcal P_{\sigma,\mathcal N}(X)=\sigma^{1/2}\mathcal N^\dagger\!\left(\mathcal N(\sigma)^{-1/2}X\mathcal N(\sigma)^{-1/2}\right)\sigma^{1/2},\quad
--   D_{\min}(\omega\Vert\tau)=-\log_2 F(\omega,\tau),\quad
--   D_{\max}(\omega\Vert\tau)=\inf\{\lambda\in\mathbb R:\omega\le2^\lambda\tau\},
--   $$
--   where $F(\omega,\tau)=\|\sqrt\omega\sqrt\tau\|_1^2$ is squared fidelity. The max-divergence infimum is extended real, so an empty set gives $+\infty$. Set $\Delta_{\min}=D_{\min}(\rho\Vert\mathcal P_{\sigma,\mathcal N}(\mathcal N(\rho)))$ and define $\Delta_{\max}$ by the same reference with $D_{\max}$.
--
--   Assume $\rho_{ABC}>0$ and define
--   $$
--   \tau=\rho_{AC}^{1/2}\rho_C^{-1/2}\rho_{BC}\rho_C^{-1/2}\rho_{AC}^{1/2},\quad
--   I_{\min}=D_{\min}(\rho\Vert\tau),\quad I_{\max}=D_{\max}(\rho\Vert\tau).
--   $$
--   Then the two equivalences hold separately:
--   $$
--   I_{\max}(A;B\mid C)_\rho=0\iff\rho\text{ is a short quantum Markov chain }A-C-B,
--   $$
--   $$
--   I_{\min}(A;B\mid C)_\rho=0\iff\rho\text{ is a short quantum Markov chain }A-C-B.
--   $$
--
--   Both one-shot information measures have the same exact Markov zero set.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 18, Corollary 19: min/max conditional information and short quantum Markov chains

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P52

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P52

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint petz marginalAB)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Renew46.P35 (HasMarkovBlocks)

/-- Corollary 19, PDF p.18, equations (5.11)–(5.12), with primary
definitions (5.4),(5.7) and both independent equivalences. -/
theorem markov_min_max {A C B : Type} [Fintype A] [Fintype C] [Fintype B]
    [DecidableEq A] [DecidableEq C] [DecidableEq B]
    [Nonempty A] [Nonempty C] [Nonempty B]
    (rho : Mat (A × (C × B))) (hrho : IsDensityMatrix rho)
    (hrhoPD : rho.PosDef) :
    (conditionalMaxInformation rho = 0 ↔ HasMarkovBlocks rho) ∧
    (conditionalMinInformation rho = 0 ↔ HasMarkovBlocks rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
