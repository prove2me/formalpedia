-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_sufficiency_renyi
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.sufficiency_renyi
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:50:56.510997+00:00
-- url     : https://prove2.me/theorems/1f5d95c4-3215-474c-8e80-d5aff5dd6ec1
-- title:
--   Theorem 14: sufficiency characterized by vanishing Renyi relative entropy differences
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
--   Sufficiency implies
--   $$
--   \Delta_a=\widetilde\Delta_a=0\quad\text{for every }a\in(0,1)\cup(1,\infty).
--   $$
--   Conversely, either $\Delta_a=0$ for some $a\in(0,1)\cup(1,2)$ or $\widetilde\Delta_a=0$ for some $a\in(1/2,1)\cup(1,\infty)$ implies sufficiency.
--
--   This characterizes sufficient channels through vanishing Rényi differences, retaining the full forward order range.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 14, Theorem 14: sufficiency characterized by vanishing Renyi relative entropy differences

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

/-- Theorem 14, PDF pp.14–17. Correction: the printed final tilde expression
omits “=0”; restored from (4.14), p.16, and the concluding proof on p.17.
The forward range is wider than either converse range. -/
theorem sufficiency_renyi {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] [Nonempty H] [Nonempty K]
    (rho sigma : Mat H) (hrho : IsDensityMatrix rho)
    (hrhoPD : rho.PosDef) (hsigmaPD : sigma.PosDef)
    (N : Superop H K) (hN : IsStrictChannel N) :
    (IsSufficient rho sigma N → ∀ a : ℝ, (0 < a ∧ a < 1) ∨ 1 < a →
      renyiDifference a rho sigma N = 0 ∧ deltaTilde a rho sigma N = 0) ∧
    (((∃ a : ℝ, ((0 < a ∧ a < 1) ∨ (1 < a ∧ a < 2)) ∧ renyiDifference a rho sigma N = 0) ∨
      (∃ a : ℝ, ((1 / 2 < a ∧ a < 1) ∨ 1 < a) ∧ deltaTilde a rho sigma N = 0)) →
      IsSufficient rho sigma N) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
