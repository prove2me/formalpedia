-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_minimum_segment
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.minimum_segment
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:45:03.210432+00:00
-- url     : https://prove2.me/theorems/f84c6cb8-5d98-42eb-b23f-0a801cf55d58
-- title:
--   Theorem 4: nearest state persists along a segment
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Let $\sigma$ be a density matrix and let a separable $\rho_*$ minimize $S(\sigma\Vert\rho)$ over separable states. For every $x\in[0,1]$, put $\sigma_x=(1-x)\sigma+x\rho_*$. Then
--
--   $$S(\sigma_x\Vert\rho_*)\le S(\sigma_x\Vert\rho)\quad(\rho\in\mathrm{Sep}).$$
--
--   The same minimizer persists on the entire closed segment, including both endpoints.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 15, Theorem 4: nearest state persists along a segment

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P42

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P42

open QAlgorithms QAlgorithms.Entanglement

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 4, PDF p.15: the same closest state persists on the closed segment.
The theorem sentence fixes (1-x)sigma+x rho; Eq.(37) interchanges the weights. -/
theorem minimum_segment {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (sigma rho : Matrix (I × J) (I × J) ℂ) (hsigma : IsDensityMatrix sigma)
    (hmin : IsMinimizer sigma rho) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    IsMinimizer (((1-x : ℝ) : ℂ) • sigma + (x : ℂ) • rho) rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
