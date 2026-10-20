-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_Q_CPTP_monotone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.Q_CPTP_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:53:51.856492+00:00
-- url     : https://prove2.me/theorems/7afd973a-4608-4df7-9842-756c90965a36
-- title:
--   CPTP monotonicity of the raw sandwiched trace
-- statement:
--   Let ρ,σ≥0 have nested supports, let Φ be CPTP between finite matrix spaces, and let α>1. For the raw sandwiched trace Qα,
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   $$
--   Q_\alpha(\Phi(\rho)\Vert\Phi(\sigma))\leq Q_\alpha(\rho\Vert\sigma).
--   $$
--
--   The raw-trace form makes joint-convexity arguments possible.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 8, Corollary III.15 (monotonicity of Q)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.8: CPTP monotonicity of the raw sandwiched trace. Q has no support-failure guard and is not a divergence or a logarithm. The actual corollary starts on PDF p.8. -/
theorem Q_CPTP_monotone (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (hsupp : SupportLE rho sigma) (Phi : Mat I →ₗ[ℂ] Mat J) (hPhi : CPTP Phi) (alpha : ℝ) (ha : 1 < alpha) :
    Q alpha (Phi rho) (Phi sigma) ≤ Q alpha rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
