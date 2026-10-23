-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_robbin_salamon_four_axioms
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.robbin_salamon_four_axioms
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:27:22.068803+00:00
-- url     : https://prove2.me/theorems/33e5503f-6555-4ef2-aee1-26170625e788
-- title:
--   Theorem 55
-- statement:
--   Across dimensions $2n$, $n\ge1$, the graph Robbin–Salamon index is a half-integer-valued assignment to every continuous symplectic path. It satisfies, and is uniquely determined by, fixed-endpoint homotopy invariance, catenation additivity, vanishing whenever the dimension of the $1$-eigenspace is constant, and the normalization
--
--   $$\mu_{\rm RS}(t\mapsto e^{tJ_0S})=\tfrac12\operatorname{Sign}S$$
--
--   for every symmetric $S$ whose eigenvalues have absolute value below $2\pi$. Singular, rank-deficient and zero $S$ are included. Every other dimension-family assignment with these properties agrees on all continuous paths. General intervals are represented by increasing affine parametrization. Product additivity is not an extra axiom in this characterization.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 52, Theorem 55

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Theorem 55, PDF pp.52,57–58: existence and dimension-family uniqueness. -/
theorem robbin_salamon_four_axioms :
    RsFourAxioms (fun _ p => robbinSalamon p) ∧
    (∀ f, RsFourAxioms f → ∀ n, 1 ≤ n → ∀ p, IsPath p 1 → f n p = robbinSalamon p) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
