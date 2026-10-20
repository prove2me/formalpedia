-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_fidelity_positive_map_monotone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.fidelity_positive_map_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:09:47.300993+00:00
-- url     : https://prove2.me/theorems/c29fb820-3940-4dd1-ba6c-872d4b226a94
-- title:
--   Root fidelity and order-one-half divergence under positive TP maps
-- statement:
--   For density operators ρ,σ and every positive trace-preserving complex-linear map Φ between arbitrary finite matrix spaces, the root fidelity F increases and, equivalently, D̃_{1/2}=−2 log F decreases:
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   $$
--   F(\Phi\rho,\Phi\sigma)\geq F(\rho,\sigma),\qquad\widetilde D_{1/2}(\Phi\rho\Vert\Phi\sigma)\leq\widetilde D_{1/2}(\rho\Vert\sigma).
--   $$
--
--   This extends the fidelity data-processing inequality to positive trace-preserving maps.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 24, Corollary A.5 The fidelity is monotone non-decreasing, or equivalently, D1/2               is monotone non-

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

/-- arXiv:1309.3228v5, PDF p.24: Root fidelity and order-one-half divergence under positive TP maps. The accepted rootFidelity is the unsquared Uhlmann fidelity. Complete positivity is not assumed. -/
theorem fidelity_positive_map_monotone (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (Phi : Mat I →ₗ[ℂ] Mat J) (hpos : Positive Phi) (htp : TP Phi) :
    rootFidelity rho sigma ≤ rootFidelity (Phi rho) (Phi sigma) ∧
    Dnew (1 / 2) (Phi rho) (Phi sigma) ≤ Dnew (1 / 2) rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
