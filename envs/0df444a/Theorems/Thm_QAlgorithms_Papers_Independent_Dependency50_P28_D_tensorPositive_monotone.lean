-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_D_tensorPositive_monotone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.D_tensorPositive_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:08:24.525931+00:00
-- url     : https://prove2.me/theorems/f3187f8a-9479-4e9d-a57e-60caded2d2b9
-- title:
--   Data processing under every tensor-stable positive TP map
-- statement:
--   Let ρ,σ≥0 with Tr ρ>0, and let Φ be a trace-preserving complex-linear map between arbitrary finite matrix spaces such that Φ^{⊗n} is positive for every n≥1. For every α>1,
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   $$
--   \widetilde D_\alpha(\Phi(\rho)\Vert\Phi(\sigma))\leq\widetilde D_\alpha(\rho\Vert\sigma).
--   $$
--
--   This yields data processing without requiring complete positivity.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 19, Corollary IV.20

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

/-- arXiv:1309.3228v5, PDF p.19: Data processing under every tensor-stable positive TP map. This returns to arbitrary PSD inputs: no trace-one, unequal-state, or support-inclusion premise. CPTP is a special case of the quantified map condition. -/
theorem D_tensorPositive_monotone (rho sigma : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) (htrace : 0 < tr rho) (Phi : Mat I →ₗ[ℂ] Mat J)
    (htp : TP Phi) (hpos : TensorPositive Phi) (alpha : ℝ) (ha : 1 < alpha) :
    Dnew alpha (Phi rho) (Phi sigma) ≤ Dnew alpha rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
