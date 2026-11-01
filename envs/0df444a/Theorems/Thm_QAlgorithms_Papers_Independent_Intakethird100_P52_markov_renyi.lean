-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_markov_renyi
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.markov_renyi
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:55:17.096326+00:00
-- url     : https://prove2.me/theorems/beb01793-cd89-4c5f-9c7b-d72de379ccb2
-- title:
--   Corollary 15: vanishing Renyi conditional information characterizes short quantum Markov chains
-- statement:
--   All Hilbert spaces below are finite dimensional and nonzero over $\mathbb C$. A density operator is positive semidefinite with trace one. Every spectral power is zero on the kernel, including zero and negative powers. Information quantities use base-two logarithms, with $\log_2 0=-\infty$; the operator logarithms in exponential formulas are natural logarithms.
--
--   Let $\rho$ be a density operator on $H$, let $\sigma\ge0$ be an operator on $H$ without a trace constraint, and let $\mathcal N:\mathcal B(H)\to\mathcal B(K)$ be CPTP. Its adjoint $\mathcal N^\dagger$ is the Hilbert–Schmidt adjoint. Write
--   $$
--   \begin{aligned}
--   K_a&=\sigma^{(1-a)/2}\mathcal N^\dagger\!\left(\mathcal N(\sigma)^{(a-1)/2}\mathcal N(\rho)^{1-a}\mathcal N(\sigma)^{(a-1)/2}\right)\sigma^{(1-a)/2},\\
--   L_a&=\sigma^{(1-a)/(2a)}\mathcal N^\dagger\!\left(\mathcal N(\sigma)^{(a-1)/(2a)}\mathcal N(\rho)^{(1-a)/a}\mathcal N(\sigma)^{(a-1)/(2a)}\right)\sigma^{(1-a)/(2a)},\\
--   R_a&=K_a^{1/(1-a)},\qquad S_a=L_a^{a/(1-a)},\\
--   \Delta_a&=\frac{\log_2\operatorname{Tr}(\rho^aK_a)}{a-1},\qquad
--   \widetilde\Delta_a=\frac{\log_2\operatorname{Tr}[(\rho^{1/2}L_a\rho^{1/2})^a]}{a-1}.
--   \end{aligned}
--   $$
--
--   Let $\rho=\rho_{ABC}$ be a tripartite density operator. Its marginals $\rho_{AC},\rho_{BC},\rho_C$ are computed by partial trace from this same state. Operators on fewer registers are extended by identities. Use tensor order $A\otimes(C\otimes B)$, and set $\sigma=\rho_{AC}\otimes I_B$ and $\mathcal N=\operatorname{Tr}_A$. Define $I_a(A;B\mid C)_\rho=\Delta_a(\rho,\sigma,\mathcal N)$ and $\widetilde I_a(A;B\mid C)_\rho=\widetilde\Delta_a(\rho,\sigma,\mathcal N)$. A short quantum Markov chain $A-C-B$ means that the whole space $H_C$ decomposes as $\bigoplus_j H_{C_{L,j}}\otimes H_{C_{R,j}}$ and $\rho=\bigoplus_j q_j\rho_{AC_{L,j}}\otimes\rho_{C_{R,j}B}$, where $q_j\ge0$, $\sum_jq_j=1$, and both factors in each block are density operators.
--
--   Assume $\rho_{ABC}>0$. If $\rho$ is a short quantum Markov chain $A-C-B$, then
--   $$
--   I_a(A;B\mid C)_\rho=\widetilde I_a(A;B\mid C)_\rho=0
--   \quad\text{for every }a\in(0,1)\cup(1,\infty).
--   $$
--   Conversely, either $I_a(A;B\mid C)_\rho=0$ for some $a\in(0,1)\cup(1,2)$ or $\widetilde I_a(A;B\mid C)_\rho=0$ for some $a\in(1/2,1)\cup(1,\infty)$ implies the Markov property.
--
--   This gives the Rényi zero-information characterization of short quantum Markov chains.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 17, Corollary 15: vanishing Renyi conditional information characterizes short quantum Markov chains

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

/-- Corollary 15, PDF p.17. Positive definite tripartite densities;
HasMarkovBlocks describes the entire conditioning register C. -/
theorem markov_renyi {A C B : Type} [Fintype A] [Fintype C] [Fintype B]
    [DecidableEq A] [DecidableEq C] [DecidableEq B]
    [Nonempty A] [Nonempty C] [Nonempty B]
    (rho : Mat (A × (C × B))) (hrho : IsDensityMatrix rho)
    (hrhoPD : rho.PosDef) :
    (HasMarkovBlocks rho → ∀ a : ℝ, (0 < a ∧ a < 1) ∨ 1 < a →
      conditionalRenyiInformation a rho = 0 ∧ conditionalRenyiTilde a rho = 0) ∧
    (((∃ a : ℝ, ((0 < a ∧ a < 1) ∨ (1 < a ∧ a < 2)) ∧ conditionalRenyiInformation a rho = 0) ∨
      (∃ a : ℝ, ((1 / 2 < a ∧ a < 1) ∨ 1 < a) ∧ conditionalRenyiTilde a rho = 0)) →
      HasMarkovBlocks rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
