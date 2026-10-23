-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_image_index_characterization
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.image_index_characterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:33:31.812625+00:00
-- url     : https://prove2.me/theorems/811ebee2-e999-44b2-aef6-13427bb4a96f
-- title:
--   Cited image-index characterization
-- statement:
--   For every $n\ge1$, fix the vertical Lagrangian $V_n=\{0\}\times\mathbb R^n$ and let $\nu_n(\gamma)=\mu_{\rm RS}(\gamma V_n,V_n)$ for continuous symplectic matrix paths on $[0,1]$ with arbitrary endpoints. This half-integer dimension family satisfies the following properties and is the unique half-integer family satisfying all of them:
--
--   1. For paths with the same matrix endpoints, fixed-endpoint homotopy holds if and only if their $\nu_n$ values agree; in particular the index is homotopy invariant.
--   2. Catenation of paths with matching endpoints is additive.
--   3. Grouped symplectic direct sums are additive across positive dimensions.
--   4. If $\dim(\gamma(t)V_n\cap V_n)=k$ is constant for $t\in[0,1]$, where $0\le k\le n$, then $\nu_n(\gamma)=0$.
--   5. For every continuous path $B(t)$ of real symmetric $n$ by $n$ matrices,
--
--   $$\nu_n\!\left(t\mapsto\begin{pmatrix}I&B(t)\\0&I\end{pmatrix}\right)
--   =\tfrac12\operatorname{Sign}B(0)-\tfrac12\operatorname{Sign}B(1).$$
--
--   Here $\operatorname{Sign}$ counts positive minus negative inertia, including zero eigenvalues. Uniqueness compares assignments on every valid path in every positive dimension. These properties characterize the image index separately from the graph index.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 58, Cited image-index characterization

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Cited image-index characterization [9], PDF p.58: satisfaction of all
five properties and uniqueness of the half-integer dimension family.
Printed: the product bullet names mu_RS2 but writes mu_RS in its equation.
Changed: every term in that bullet is mu_RS2, as forced by its subject and
Theorem 45(3). This correction requires fresh independent moderation. -/
theorem image_index_characterization :
    ImageIndexAxioms (fun _ p => robbinSalamonVertical p) ∧
    (∀ f, ImageIndexAxioms f → ∀ n, 1 ≤ n →
      ∀ p : ℝ → GroupedRealMatrix n, IsPath p 1 → f n p = robbinSalamonVertical p) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
