-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_output_space_equality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.output_space_equality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:57:37.653512+00:00
-- url     : https://prove2.me/theorems/4738b5a7-7e27-45e6-9f3b-beb4dc0cb85a
-- title:
--   Proposition 20: alternative output-space equality condition
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
--   Assume $\rho>0$, $\sigma>0$, and that $\mathcal N$ is strict: $\mathcal N(X)>0$ for every $X>0$. The channel is sufficient for $(\rho,\sigma)$ when one CPTP map $\mathcal R$ satisfies $\mathcal R(\mathcal N(\rho))=\rho$ and $\mathcal R(\mathcal N(\sigma))=\sigma$.
--
--   Define the output-space operator
--   $$
--   P_a=\left[\mathcal N(\sigma)^{(a-1)/2}\mathcal N\!\left(\sigma^{(1-a)/2}\rho^a\sigma^{(1-a)/2}\right)\mathcal N(\sigma)^{(a-1)/2}\right]^{1/a}.
--   $$
--   For every $1<a<2$,
--   $$
--   \Delta_a\ge0,\qquad\Delta_a=0\iff P_a=\mathcal N(\rho).
--   $$
--   The supporting inequality (A.16) also gives $\operatorname{Tr}P_a\ge1$. For every $a>1$, $\widetilde\Delta_a\ge0$.
--
--   This is a distinct equality criterion on the output algebra, together with its inventoried supporting trace bound.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 19, Proposition 20: alternative output-space equality condition

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

/-- Proposition 20, PDF p.19, equation (A.1): the distinct output-space
equality criterion, its supporting trace bound (A.16), p.21, and
sandwiched nonnegativity at every order above one. -/
theorem output_space_equality {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] [Nonempty H] [Nonempty K]
    (rho sigma : Mat H) (hrho : IsDensityMatrix rho)
    (hrhoPD : rho.PosDef) (hsigmaPD : sigma.PosDef)
    (N : Superop H K) (hN : IsStrictChannel N) :
    (∀ a : ℝ, 1 < a ∧ a < 2 →
      0 ≤ renyiDifference a rho sigma N ∧
      (renyiDifference a rho sigma N = 0 ↔ outputReference a rho sigma N = N rho) ∧
      1 ≤ tr (outputReference a rho sigma N)) ∧
    (∀ a : ℝ, 1 < a → 0 ≤ deltaTilde a rho sigma N) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
