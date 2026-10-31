-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P42_relativeEntanglement_convex
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P42.relativeEntanglement_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:45:42.46731+00:00
-- url     : https://prove2.me/theorems/8d3fae6c-b5ee-45d5-8694-f40a72134767
-- title:
--   Theorem 5: convexity
-- statement:
--   All local registers are nonzero and finite-dimensional. Density matrices are positive semidefinite with trace one. Entropies use natural logarithms, $0\ln0=0$, and Umegaki relative entropy $S(\sigma\Vert\rho)$ is $+\infty$ on failure of support inclusion. The relative entropy of entanglement is $E_R(\sigma)=\inf_{\rho\in\mathrm{Sep}}S(\sigma\Vert\rho)$, where separability is across the specified Alice:Bob cut.
--
--   For density matrices $\sigma_1,\sigma_2$ on the same bipartite register and weights $x_1,x_2\ge0$ with $x_1+x_2=1$,
--
--   $$E_R(x_1\sigma_1+x_2\sigma_2)\le x_1E_R(\sigma_1)+x_2E_R(\sigma_2).$$
--
--   This is convexity of the relative-entropy-generated measure.
-- source:
--   Entanglement Measures and Purification Procedures, arXiv:quant-ph/9707035v2, PDF p. 15, Theorem 5: convexity

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

/-- Theorem 5, PDF pp.15–16: convexity of relative entropy of entanglement. -/
theorem relativeEntanglement_convex {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (sigma tau : Matrix (I × J) (I × J) ℂ)
    (hsigma : IsDensityMatrix sigma) (htau : IsDensityMatrix tau)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x+y=1) :
    relativeEntanglementNats ((x : ℂ) • sigma + (y : ℂ) • tau) ≤
      (x : EReal) * relativeEntanglementNats sigma + (y : EReal) * relativeEntanglementNats tau := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P42

end
