-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_renyi_reference_trace_bounds
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.renyi_reference_trace_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:51:49.323217+00:00
-- url     : https://prove2.me/theorems/330130f1-eb67-433e-807d-b0317f0433e1
-- title:
--   Lemma 9: trace bounds for two Renyi reference operators
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
--   Then
--   $$
--   \operatorname{Tr}R_a\le1\quad(0<a<1),\qquad
--   \operatorname{Tr}S_a\le1\quad(1/2<a<1).
--   $$
--   If in addition $\rho,\sigma,\mathcal N(\rho),\mathcal N(\sigma)$ are positive definite, the first inequality also holds for $1<a<2$, and the second for every $a>1$. Global strictness is not required.
--
--   These trace bounds control the normalization of the two computed reference operators.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 10, Lemma 9: trace bounds for two Renyi reference operators

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

/-- Lemma 9, PDF pp.10–13, equations (3.23)–(3.24), all four order regimes.
Above one only the named inputs and outputs must be positive definite. -/
theorem renyi_reference_trace_bounds {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] [Nonempty H] [Nonempty K]
    (rho sigma : Mat H) (hrho : IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (N : Superop H K) (hN : IsChannel N) :
    (∀ a : ℝ, 0 < a ∧ a < 1 → tr (renyiReference a rho sigma N) ≤ 1) ∧
    (∀ a : ℝ, 1 / 2 < a ∧ a < 1 → tr (sandwichedReference a rho sigma N) ≤ 1) ∧
    ((rho.PosDef ∧ sigma.PosDef ∧ (N rho).PosDef ∧ (N sigma).PosDef) →
      (∀ a : ℝ, 1 < a ∧ a < 2 → tr (renyiReference a rho sigma N) ≤ 1) ∧
      (∀ a : ℝ, 1 < a → tr (sandwichedReference a rho sigma N) ≤ 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
