-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_robbin_salamon_seven_axioms
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.robbin_salamon_seven_axioms
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:27:48.050549+00:00
-- url     : https://prove2.me/theorems/a4fd9b27-268d-4117-b2dc-e098d321b92d
-- title:
--   Lemma 56
-- statement:
--   The graph Robbin–Salamon index, as a dimension-family of half-integer assignments on all continuous symplectic paths, satisfies and is uniquely characterized by: agreement with the classical index on admissible paths; naturality under time-dependent symplectic conjugation; fixed-endpoint homotopy invariance; catenation additivity; symplectic direct-sum additivity; vanishing for constant $1$-eigenspace dimension; and the shear rule
--
--   $$\mu_{\rm RS}\left(t\mapsto\begin{pmatrix}I&-tB\\0&I\end{pmatrix}\right)=\tfrac12\operatorname{Sign}B\qquad(B=B^\mathsf T).$$
--
--   Every dimension-family assignment with all seven properties equals the constructed graph index on every continuous path. Arbitrarily degenerate endpoints are included. This retains generalization, naturality and product as separate requirements.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 53, Lemma 56

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Lemma 56, PDF p.53: all seven properties retained, including -tB. -/
theorem robbin_salamon_seven_axioms :
    RsSevenAxioms (fun _ p => robbinSalamon p) ∧
    (∀ f, RsSevenAxioms f → ∀ n, 1 ≤ n → ∀ p, IsPath p 1 → f n p = robbinSalamon p) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
