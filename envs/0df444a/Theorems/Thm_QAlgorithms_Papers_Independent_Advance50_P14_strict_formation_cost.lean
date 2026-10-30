-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_strict_formation_cost
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.strict_formation_cost
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:19:53.534891+00:00
-- url     : https://prove2.me/theorems/eb49b2c7-b13a-4f73-a1c0-ef4fc4ad82f5
-- title:
--   Section V, equation (21): exact-map formation cost
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. Let $R(\rho)$ be standard robustness: the least nonnegative $s$ such that $(\rho+s\pi)/(1+s)$ is separable for a separable noise state $\pi$. Let $LR=\log_2(1+R)$, $LR^\epsilon(\rho)=\min_{\|\widetilde\rho-\rho\|_1\le\epsilon}LR(\widetilde\rho)$ over density matrices, and define $LH(\rho)=\inf_{\epsilon_n\to0}\limsup_n LR^{\epsilon_n}(\rho^{\otimes n})/n$. Then
--
--   $$E_C^{\rm ne}(\rho)=LH(\rho).$$
--
--   The cost uses exactly separability-preserving CPTP maps at every blocklength. This is distinct from global robustness, whose noise may be entangled. The printed unrestricted real mixing weight is corrected to a nonnegative weight.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 16, Section V, equation (21): exact-map formation cost

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.16, Eq.(21) and following sentence: strict formation cost is LH,
the smoothed regularization of STANDARD robustness, with separable noise. -/
theorem strict_formation_cost {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (hrho : IsDensityMatrix rho) :
    asymptoticFormationCost .strict A rho = smoothedRegularizedRobustness true A rho := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
