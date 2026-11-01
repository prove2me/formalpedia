-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_renyi_nonnegative_iff_reference
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.renyi_nonnegative_iff_reference
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:54:26.818622+00:00
-- url     : https://prove2.me/theorems/0689b7aa-33ea-4e9f-a7a3-b3d5d035d43b
-- title:
--   Proposition 13: nonnegativity and exact reference equality conditions
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
--   For the indicated ranges,
--   $$
--   \begin{aligned}
--   0<a<1 &: \quad\Delta_a\ge0,\qquad (\Delta_a=0\iff\rho=R_a),\\
--   1/2<a<1 &: \quad\widetilde\Delta_a\ge0,\qquad (\widetilde\Delta_a=0\iff\rho=S_a).
--   \end{aligned}
--   $$
--   If $\rho,\sigma,\mathcal N(\rho),\mathcal N(\sigma)>0$, the first pair of conclusions also holds for $1<a<2$, and the second for every $a>1$.
--
--   Nonnegativity and exact equality to the computed reference are both parts of the result.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 14, Proposition 13: nonnegativity and exact reference equality conditions

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

/-- Proposition 13, PDF p.14, equations (3.56)–(3.59). Each equality condition
is a conclusion. No support containment or strictness is added below one. -/
theorem renyi_nonnegative_iff_reference {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] [Nonempty H] [Nonempty K]
    (rho sigma : Mat H) (hrho : IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (N : Superop H K) (hN : IsChannel N) :
    (∀ a : ℝ, 0 < a ∧ a < 1 →
      0 ≤ renyiDifference a rho sigma N ∧
      (renyiDifference a rho sigma N = 0 ↔ rho = renyiReference a rho sigma N)) ∧
    (∀ a : ℝ, 1 / 2 < a ∧ a < 1 →
      0 ≤ deltaTilde a rho sigma N ∧
      (deltaTilde a rho sigma N = 0 ↔ rho = sandwichedReference a rho sigma N)) ∧
    ((rho.PosDef ∧ sigma.PosDef ∧ (N rho).PosDef ∧ (N sigma).PosDef) →
      (∀ a : ℝ, 1 < a ∧ a < 2 →
        0 ≤ renyiDifference a rho sigma N ∧
        (renyiDifference a rho sigma N = 0 ↔ rho = renyiReference a rho sigma N)) ∧
      (∀ a : ℝ, 1 < a →
        0 ≤ deltaTilde a rho sigma N ∧
        (deltaTilde a rho sigma N = 0 ↔ rho = sandwichedReference a rho sigma N))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
