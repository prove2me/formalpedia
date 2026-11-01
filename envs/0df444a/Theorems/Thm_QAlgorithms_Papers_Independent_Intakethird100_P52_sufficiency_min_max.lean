-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_sufficiency_min_max
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.sufficiency_min_max
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:56:18.850166+00:00
-- url     : https://prove2.me/theorems/eefc4f7a-ed69-417f-8d20-17474a75e322
-- title:
--   Theorem 17: min/max entropy differences and channel sufficiency
-- statement:
--   All Hilbert spaces below are finite dimensional and nonzero over $\mathbb C$. A density operator is positive semidefinite with trace one. Every spectral power is zero on the kernel, including zero and negative powers. Information quantities use base-two logarithms, with $\log_2 0=-\infty$; the operator logarithms in exponential formulas are natural logarithms.
--
--   Let $\rho>0$ be a density operator, $\sigma>0$ arbitrary, and $\mathcal N$ strict CPTP. Sufficiency means existence of a common CPTP recovery of both $\rho$ and $\sigma$.
--
--   The Petz map and min/max divergences are
--   $$
--   \mathcal P_{\sigma,\mathcal N}(X)=\sigma^{1/2}\mathcal N^\dagger\!\left(\mathcal N(\sigma)^{-1/2}X\mathcal N(\sigma)^{-1/2}\right)\sigma^{1/2},\quad
--   D_{\min}(\omega\Vert\tau)=-\log_2 F(\omega,\tau),\quad
--   D_{\max}(\omega\Vert\tau)=\inf\{\lambda\in\mathbb R:\omega\le2^\lambda\tau\},
--   $$
--   where $F(\omega,\tau)=\|\sqrt\omega\sqrt\tau\|_1^2$ is squared fidelity. The max-divergence infimum is extended real, so an empty set gives $+\infty$. Set $\Delta_{\min}=D_{\min}(\rho\Vert\mathcal P_{\sigma,\mathcal N}(\mathcal N(\rho)))$ and define $\Delta_{\max}$ by the same reference with $D_{\max}$.
--
--   Then
--   $$
--   \Delta_{\min}\ge0,\qquad\Delta_{\max}\ge0,\qquad
--   (\Delta_{\min}=0\iff\mathcal N\text{ is sufficient}),\qquad
--   (\Delta_{\max}=0\iff\mathcal N\text{ is sufficient}).
--   $$
--
--   Each min/max entropy difference separately detects sufficiency.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 17, Theorem 17: min/max entropy differences and channel sufficiency

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

/-- Theorem 17, PDF p.17, equation (5.3): both nonnegativities and each
individual iff-zero condition. Recovery of rho is not assumed. -/
theorem sufficiency_min_max {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] [Nonempty H] [Nonempty K]
    (rho sigma : Mat H) (hrho : IsDensityMatrix rho)
    (hrhoPD : rho.PosDef) (hsigmaPD : sigma.PosDef)
    (N : Superop H K) (hN : IsStrictChannel N) :
    0 ≤ deltaMin rho sigma N ∧ 0 ≤ deltaMax rho sigma N ∧
    (deltaMin rho sigma N = 0 ↔ IsSufficient rho sigma N) ∧
    (deltaMax rho sigma N = 0 ↔ IsSufficient rho sigma N) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
