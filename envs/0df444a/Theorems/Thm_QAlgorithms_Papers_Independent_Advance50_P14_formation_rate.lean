-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P14_formation_rate
-- name    : QAlgorithms.Papers.Independent.Advance50.P14.formation_rate
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:16:12.936317+00:00
-- url     : https://prove2.me/theorems/8cbcf0f8-3ff0-4c95-a0c0-e5c0ec12925d
-- title:
--   Proposition IV.2, equation (9): formation rate
-- statement:
--   All systems are finite-dimensional complex multipartite systems with at least two parties and positive local dimensions. Every state is positive semidefinite with trace one. Separability means a convex mixture of products across all parties. Logarithms are base two, and the trace norm has no factor of one half. Bell pairs shared by the first two parties are the currency. Integer copy counts are nonnegative, blocklengths are positive, and both approximation error and the uniform global-robustness leakage tend to zero absolutely. For every multipartite state $\rho$, the asymptotically non-entangling formation cost satisfies
--
--   $$E_C^{\rm ane}(\rho)=E_R^\infty(\rho).$$
--
--   The cost is an infimum over feasible integer Bell-pair count sequences, without an attainment assumption. This is the separately numbered formation half of the main result.
-- source:
--   A reversible theory of entanglement and its relation to the second law, arXiv:0710.5827v3, PDF p. 9, Proposition IV.2, equation (9): formation rate

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P14

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis)

open scoped Matrix ComplexOrder ENNReal NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P14

/-- PDF p.9, Proposition IV.2, Eq.(9): arbitrary multipartite formation.
The final d_2 in its printed dimension list is an index typo, as confirmed by
Theorem I and this proposition's proof. No optimizing sequence is assumed. -/
theorem formation_rate {m : ℕ} (A : MultipartiteRegister m) (rho : PartyOperator A)
    (hrho : IsDensityMatrix rho) :
    asymptoticFormationCost .ane A rho = ENNReal.ofReal (regularizedMultipartiteEntanglement A rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P14

end
