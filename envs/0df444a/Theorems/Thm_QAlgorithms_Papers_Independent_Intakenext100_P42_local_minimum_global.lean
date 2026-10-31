-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_local_minimum_global
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.local_minimum_global
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:49:12.630983+00:00
-- url     : https://prove2.me/theorems/11695264-e4e5-4d92-8afc-76dec3b4ea69
-- title:
--   Unnumbered: matrix local minima are global
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   Fix a density matrix $\sigma$ and a separable state $\rho_*$ with finite $S(\sigma\Vert\rho_*)$. If $\rho_*$ is a local minimum of $\rho\mapsto S(\sigma\Vert\rho)$ within the separable matrix domain in its finite-dimensional topology, then
--
--   $$S(\sigma\Vert\rho_*)\le S(\sigma\Vert\rho)\quad(\rho\in\mathrm{Sep}).$$
--
--   This is the convex-matrix-domain minimum principle for the extended support-aware objective.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 21, Unnumbered: matrix local minima are global

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

/-- PDF p.21: a finite local minimum in the convex MATRIX domain is global.
No stationarity or local minimality in angular coordinates is substituted. -/
theorem local_minimum_global {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (sigma rho : Matrix (I × J) (I × J) ℂ) (hsigma : IsDensityMatrix sigma)
    (hrho : IsSeparableDensity rho) (hfinite : relativeEntropy sigma rho ≠ ⊤)
    (hlocal : IsLocalMinOn (relativeEntropy sigma)
      {tau : Matrix (I × J) (I × J) ℂ | IsSeparableDensity tau} rho) :
    IsMinimizer sigma rho := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
