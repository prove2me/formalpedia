-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_renyi_difference_comparison
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.renyi_difference_comparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:59:23.926186+00:00
-- url     : https://prove2.me/theorems/d3a9bf39-64c2-4f38-be80-4e40873e5231
-- title:
--   Appendix A (A.28): comparison of the two Renyi differences
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
--   For $a>1$ set $a^\prime=(2a-1)/a$, so $1<a^\prime<2$. Then
--   $$
--   \widetilde\Delta_a(\rho,\sigma,\mathcal N)\ge\Delta_{a^\prime}(\rho,\sigma,\mathcal N).
--   $$
--
--   This compares the sandwiched difference to a Petz-type difference at the transformed order.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 22, Appendix A (A.28): comparison of the two Renyi differences

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

/-- Appendix A, PDF p.22, equation (A.28), inheriting Proposition 20
hypotheses. Primary (1.17)/(A.17) fixes the scale despite the auxiliary typo
in (A.19); the comparison has coefficient one. -/
theorem renyi_difference_comparison {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] [Nonempty H] [Nonempty K]
    (rho sigma : Mat H) (hrho : IsDensityMatrix rho)
    (hrhoPD : rho.PosDef) (hsigmaPD : sigma.PosDef)
    (N : Superop H K) (hN : IsStrictChannel N)
    (a : ℝ) (ha : 1 < a) :
    renyiDifference ((2 * a - 1) / a) rho sigma N ≤ deltaTilde a rho sigma N := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
