-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_sharpFixedTableau
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.sharpFixedTableau
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:41:24.234691+00:00
-- url     : https://prove2.me/theorems/b4142c9d-98ad-4f50-9703-22ae295ed2c4
-- title:
--   Sharp bound on every fixed tableau space
-- statement:
--   Let $\nu$ have $N\ge2$ boxes, let $d\ge c_1$, and fix any standard tableau $t$ of shape $\nu$. Suppose the label $N$ occupies the removable box $(c_l,l)$. Put $q_l=\prod_{i=1}^{c_l-1}(1-1/h_{(i,l)})$, where hooks are those of $\nu$. Then
--
--   $$
--   \forall\psi\in\operatorname{Im}P_t,\quad\|\psi\|=1\Longrightarrow\lambda_1(\psi)^2\le q_l,
--   \qquad
--   \exists\psi\in\operatorname{Im}P_t,\quad\|\psi\|=1,\ \lambda_1(\psi)^2=q_l.
--   $$
--
--   Every fixed tableau space therefore has its own attained sharp bound, determined by its last box. Equality with the global maximum over all corners is not asserted.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 6, Remark 3; proof pp.15–19

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Remark 3 and its proof, arXiv:1805.00364v2 PDF pp.6,15-19.
Each fixed tableau has the bound attached to its final box; the bound is attained. -/
theorem sharpFixedTableau {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (t : Filling n) (ht : IsTableau nu.val t) :
    (∀ psi ∈ tableauSpace d t, ‖psi‖ = 1 →
      largestSchmidtSq psi ≤ cornerBound nu.val (lastBox t (by omega))) ∧
    (∃ psi ∈ tableauSpace d t, ‖psi‖ = 1 ∧
      largestSchmidtSq psi = cornerBound nu.val (lastBox t (by omega))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
