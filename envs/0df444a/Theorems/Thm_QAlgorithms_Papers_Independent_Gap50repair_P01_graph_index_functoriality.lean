-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_graph_index_functoriality
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.graph_index_functoriality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:33:08.046668+00:00
-- url     : https://prove2.me/theorems/4da55fb3-cf1b-4748-889e-0cc866d85e87
-- title:
--   Cited graph-index homotopy, catenation and product properties
-- statement:
--   For every $n\ge1$, let $\mu_{\rm RS}(\gamma)$ denote the graph Robbin–Salamon index of a continuous path $\gamma:[0,1]\to\operatorname{Sp}(2n,\mathbb R)$. The graph lies in the doubled symplectic space with form $-\Omega_0\oplus\Omega_0$, with the diagonal as reference. Arbitrary and possibly degenerate endpoints are allowed. The index takes values in $\frac12\mathbb Z$, is invariant under fixed-endpoint homotopies, and satisfies
--
--   $$\mu_{\rm RS}(\gamma*\eta)=\mu_{\rm RS}(\gamma)+\mu_{\rm RS}(\eta),\qquad
--   \mu_{\rm RS}(\gamma\oplus\eta)=\mu_{\rm RS}(\gamma)+\mu_{\rm RS}(\eta).$$
--
--   For catenation $*$ the endpoint of $\gamma$ equals the initial point of $\eta$, and both halves are affinely reparametrized to $[0,1]$. The product formula uses the grouped symplectic direct sum of positive summand dimensions. These functorial properties transfer the corresponding Lagrangian-index rules to matrix paths.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 47, Cited graph-index homotopy, catenation and product properties

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Cited graph-index functoriality [9], PDF p.47: half-integer range,
fixed-endpoint homotopy invariance, matching-endpoint catenation and product. -/
theorem graph_index_functoriality :
    IsHalfIntegerFamily (fun _ p => robbinSalamon p) ∧
    (∀ n, 1 ≤ n → ∀ p q : ℝ → GroupedRealMatrix n,
      IsPath p 1 → IsPath q 1 → FixedHomotopic p q 1 →
      robbinSalamon p = robbinSalamon q) ∧
    (∀ n, 1 ≤ n → ∀ p q : ℝ → GroupedRealMatrix n,
      IsPath p 1 → IsPath q 1 → p 1 = q 0 →
      robbinSalamon (catenate p q) = robbinSalamon p + robbinSalamon q) ∧
    RsProduct (fun _ p => robbinSalamon p) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
