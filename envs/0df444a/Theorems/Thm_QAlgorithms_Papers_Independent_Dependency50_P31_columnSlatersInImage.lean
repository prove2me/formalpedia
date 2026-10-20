-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_columnSlatersInImage
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.columnSlatersInImage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:39:44.626693+00:00
-- url     : https://prove2.me/theorems/b3adaa46-f9b2-4b56-a6fc-6a1841080100
-- title:
--   Column Slater products lie in the tableau image
-- statement:
--   Let $t$ be a column-ordered standard tableau of a nonempty Young diagram $\nu$ with $N$ boxes and column lengths $c_1,\ldots,c_{r_1}$. Let $u_1,\ldots,u_{c_1}\in\mathbb C^d$ be orthonormal. Write $|u_1\wedge\cdots\wedge u_m\rangle$ for the normalized antisymmetric sum with coefficient $1/\sqrt{m!}$. Then
--
--   $$
--   \bigotimes_{j=1}^{r_1}|u_1\wedge\cdots\wedge u_{c_j}\rangle
--   \in\operatorname{Im}P_t.
--   $$
--
--   The factors occupy consecutive physical columns in column order. This constructs explicit vectors in the tableau image; the case $N=1$ is included.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 17, Lemma 13, equation (61); proof p.18

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Lemma 13, arXiv:1805.00364v2 PDF pp.17-18, equation (61).
The last Slater has c_{r_1} particles, and every Slater has normalization 1/sqrt(c!). -/
theorem columnSlatersInImage {d n : ℕ} (hn : 1 ≤ n) (nu : Schur.Partition d n)
    (t : Filling n) (ht : IsTableau nu.val t) (horder : ColumnOrdered t)
    (u : ℕ → EuclideanSpace ℂ (Fin d))
    (hu : Orthonormal ℂ (fun i : Fin (nu.val.colLen 0) => u i.val)) :
    columnProduct u (columnHeights nu.val) n ∈ tableauSpace d t := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
