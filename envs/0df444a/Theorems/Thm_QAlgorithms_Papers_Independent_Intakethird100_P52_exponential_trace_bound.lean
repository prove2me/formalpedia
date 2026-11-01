-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P52_exponential_trace_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P52.exponential_trace_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:53:00.00683+00:00
-- url     : https://prove2.me/theorems/09ac2081-38bf-4510-910a-16ab7b4ac80b
-- title:
--   Corollary 10: exponential trace inequality resolving the Ruskai question
-- statement:
--   All Hilbert spaces below are finite dimensional and nonzero over $\mathbb C$. A density operator is positive semidefinite with trace one. Every spectral power is zero on the kernel, including zero and negative powers. Information quantities use base-two logarithms, with $\log_2 0=-\infty$; the operator logarithms in exponential formulas are natural logarithms.
--
--   Let $\rho>0$ be a density operator, let $\sigma>0$ be arbitrary, and let $\mathcal N:\mathcal B(H)\to\mathcal B(K)$ be a strict CPTP map. Then
--   $$
--   \operatorname{Tr}\exp\!\left(\log\sigma+\mathcal N^\dagger(\log\mathcal N(\rho)-\log\mathcal N(\sigma))\right)\le1.
--   $$
--   Here the exponential is the ordinary exponential of a Hermitian operator and satisfies $\exp(0)=I$.
--
--   This gives the exponential trace inequality posed by Ruskai.
-- source:
--   Quantum Markov chains, sufficiency of quantum channels, and Renyi information measures, arXiv:1501.05636v4, PDF p. 13, Corollary 10: exponential trace inequality resolving the Ruskai question

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

/-- Corollary 10, PDF p.13, equation (3.50). Natural logarithms and ordinary
exponential of the Hermitian exponent; exp(0)=I even on its zero eigenspace. -/
theorem exponential_trace_bound {H K : Type} [Fintype H] [Fintype K]
    [DecidableEq H] [DecidableEq K] [Nonempty H] [Nonempty K]
    (rho sigma : Mat H) (hrho : IsDensityMatrix rho)
    (hrhoPD : rho.PosDef) (hsigmaPD : sigma.PosDef)
    (N : Superop H K) (hN : IsStrictChannel N) :
    tr (cfc Real.exp (cfc Real.log sigma +
      channelAdjoint N (cfc Real.log (N rho) - cfc Real.log (N sigma)))) ≤ 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P52

end
