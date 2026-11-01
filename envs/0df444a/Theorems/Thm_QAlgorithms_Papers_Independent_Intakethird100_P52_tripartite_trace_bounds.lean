-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_tripartite_trace_bounds
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.tripartite_trace_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:53:43.661327+00:00
-- url     : https://prove2.me/theorems/5ea05723-f3fe-404a-9335-23971b523b02
-- title:
--   Corollary 11: tripartite trace inequalities
-- statement:
--   All Hilbert spaces below are finite dimensional and nonzero over $\mathbb C$. A density operator is positive semidefinite with trace one. Every spectral power is zero on the kernel, including zero and negative powers. Information quantities use base-two logarithms, with $\log_2 0=-\infty$; the operator logarithms in exponential formulas are natural logarithms.
--
--   Let $\rho=\rho_{ABC}$ be a tripartite density operator. Its marginals $\rho_{AC},\rho_{BC},\rho_C$ are computed by partial trace from this same state. Operators on fewer registers are extended by identities. Use tensor order $A\otimes(C\otimes B)$, and set $\sigma=\rho_{AC}\otimes I_B$ and $\mathcal N=\operatorname{Tr}_A$. Define $I_a(A;B\mid C)_\rho=\Delta_a(\rho,\sigma,\mathcal N)$ and $\widetilde I_a(A;B\mid C)_\rho=\widetilde\Delta_a(\rho,\sigma,\mathcal N)$. A short quantum Markov chain $A-C-B$ means that the whole space $H_C$ decomposes as $\bigoplus_j H_{C_{L,j}}\otimes H_{C_{R,j}}$ and $\rho=\bigoplus_j q_j\rho_{AC_{L,j}}\otimes\rho_{C_{R,j}B}$, where $q_j\ge0$, $\sum_jq_j=1$, and both factors in each block are density operators.
--
--   Define
--   $$
--   \begin{aligned}
--   R_a^{ABC}&=\left(\rho_{AC}^{(1-a)/2}\rho_C^{(a-1)/2}\rho_{BC}^{1-a}\rho_C^{(a-1)/2}\rho_{AC}^{(1-a)/2}\right)^{1/(1-a)},\\
--   S_a^{ABC}&=\left(\rho_{AC}^{(1-a)/(2a)}\rho_C^{(a-1)/(2a)}\rho_{BC}^{(1-a)/a}\rho_C^{(a-1)/(2a)}\rho_{AC}^{(1-a)/(2a)}\right)^{a/(1-a)}.
--   \end{aligned}
--   $$
--   Then $\operatorname{Tr}R_a^{ABC}\le1$ for $0<a<1$ and $\operatorname{Tr}S_a^{ABC}\le1$ for $1/2<a<1$. If $\rho_{ABC}>0$, the respective bounds extend to $1<a<2$ and every $a>1$.
--
--   These are the tripartite versions of the channel reference trace bounds.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 13, Corollary 11: tripartite trace inequalities

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

/-- Corollary 11, PDF p.13, equations (3.52)–(3.53). The displayed products
are the computed R_alpha/S_alpha for sigma=rho_AC tensor I_B, N=Tr_A,
by (1.21); all marginals come from the same rho in order A x (C x B). -/
theorem tripartite_trace_bounds {A C B : Type} [Fintype A] [Fintype C] [Fintype B]
    [DecidableEq A] [DecidableEq C] [DecidableEq B]
    [Nonempty A] [Nonempty C] [Nonempty B]
    (rho : Mat (A × (C × B))) (hrho : IsDensityMatrix rho) :
    (∀ a : ℝ, 0 < a ∧ a < 1 →
      tr (renyiReference a rho (conditionalSigma rho) traceLeft) ≤ 1) ∧
    (∀ a : ℝ, 1 / 2 < a ∧ a < 1 →
      tr (sandwichedReference a rho (conditionalSigma rho) traceLeft) ≤ 1) ∧
    (rho.PosDef →
      (∀ a : ℝ, 1 < a ∧ a < 2 →
        tr (renyiReference a rho (conditionalSigma rho) traceLeft) ≤ 1) ∧
      (∀ a : ℝ, 1 < a →
        tr (sandwichedReference a rho (conditionalSigma rho) traceLeft) ≤ 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
