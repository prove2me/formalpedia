-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_robbin_salamon_six_axioms
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.robbin_salamon_six_axioms
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:28:12.312774+00:00
-- url     : https://prove2.me/theorems/54c357ac-4b1f-45ae-8d56-775e2a2b21ac
-- title:
--   Lemma 57
-- statement:
--   The graph Robbin–Salamon index on continuous symplectic paths, across positive dimensions, satisfies and is uniquely determined by fixed-endpoint homotopy invariance, catenation additivity, vanishing for constant $1$-eigenspace dimension, direct-sum additivity, and the two normalizations
--
--   $$\mu_{\rm RS}(e^{tJ_0S})=\tfrac12\operatorname{Sign}S,\qquad \mu_{\rm RS}\left(\begin{pmatrix}I&-tB\\0&I\end{pmatrix}\right)=\tfrac12\operatorname{Sign}B.$$
--
--   Here $S$ is symmetric and nonsingular with all eigenvalues of modulus below $2\pi$, whereas $B$ is any symmetric matrix, including singular ones. Every other half-integer family with these six properties agrees on all continuous paths. Unlike Theorem 55, product remains an axiom and the two normalizations are distinct.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 56, Lemma 57

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 57, PDF pp.56–57: product remains an axiom; the normalizations stay distinct. -/
theorem robbin_salamon_six_axioms :
    RsSixAxioms (fun _ p => robbinSalamon p) ∧
    (∀ f, RsSixAxioms f → ∀ n, 1 ≤ n → ∀ p, IsPath p 1 → f n p = robbinSalamon p) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
