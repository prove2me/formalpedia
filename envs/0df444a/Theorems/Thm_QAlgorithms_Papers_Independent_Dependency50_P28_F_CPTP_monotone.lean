-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_F_CPTP_monotone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.F_CPTP_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:52:21.393988+00:00
-- url     : https://prove2.me/theorems/75b17bb4-1e8b-448e-9473-ad53c283f609
-- title:
--   CPTP monotonicity of F
-- statement:
--   For ρ,σ≥0 with nested supports, any CPTP map Φ between arbitrary finite input and output spaces, and any α>1,
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   $$
--   F_\alpha(\Phi(\rho)\Vert\Phi(\sigma))\leq F_\alpha(\rho\Vert\sigma).
--   $$
--
--   This is data processing for the unnormalized logarithmic functional.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 7, Corollary III.13 (monotonicity)

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

/-- arXiv:1309.3228v5, PDF p.7: CPTP monotonicity of F. -/
theorem F_CPTP_monotone (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (hsupp : SupportLE rho sigma) (Phi : Mat I →ₗ[ℂ] Mat J) (hPhi : CPTP Phi) (alpha : ℝ) (ha : 1 < alpha) :
    F alpha (Phi rho) (Phi sigma) ≤ F alpha rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
