-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_lemma_8_4
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.lemma_8_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:00:41.368594+00:00
-- url     : https://prove2.me/theorems/9a344a2c-facc-45f8-887b-371f491c55c5
-- title:
--   Countable disjoint ball refinements over local fields
-- statement:
--   Let $\mathbb K$ be a nondiscrete locally compact totally disconnected field, with a compatible ultrametric absolute value fixed as in Section 8.2. Give $\mathbb K^d$ the maximum norm, where $d>0$. Let $U\subseteq\mathbb K^d$ be nonempty and open, and $(U_i)_{i\in I}$ an open cover of $U$. There are a countable index set $J$, positive real radii $r_j$ and centers $a_j\in U$ such that
--
--   $$
--   U=\bigsqcup_{j\in J}B_{r_j}(a_j),\qquad
--   (\forall j\in J)(\exists i\in I)\ B_{r_j}(a_j)\subseteq U_i.
--   $$
--
--   All balls are taken in the maximum norm. This gives a disjoint countable refinement subordinate to an arbitrary open cover. In Lean the countable index set is represented by a subset of $\mathbb N$; the field's norm represents precisely the compatible absolute value fixed in the source.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 48, Lemma 8.4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Lemma 8.4, PDF p.48, with the compatible ultrametric absolute value and
maximum norm fixed in Section 8.2, PDF p.47. The countable index set is represented
as a subset of the natural numbers, allowing finite partitions as well. -/
theorem lemma_8_4
    (K : Type u) [NontriviallyNormedField K] [LocallyCompactSpace K]
    [TotallyDisconnectedSpace K]
    (hultra : ∀ x y : K, ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (d : ℕ) (hd : 0 < d) (U : Set (Fin d → K))
    (hU : IsOpen U) (hne : U.Nonempty)
    {I : Type*} (Ui : I → Set (Fin d → K))
    (hUi : ∀ i, IsOpen (Ui i)) (hsub : ∀ i, Ui i ⊆ U)
    (hcover : U = ⋃ i, Ui i) :
    ∃ (J : Set ℕ) (r : J → ℝ) (a : J → (Fin d → K)),
      (∀ j, 0 < r j ∧ a j ∈ U) ∧
      U = ⋃ j, Metric.ball (a j) (r j) ∧
      (Pairwise fun i j : J => Disjoint (Metric.ball (a i) (r i))
        (Metric.ball (a j) (r j))) ∧
      (∀ j, ∃ i, Metric.ball (a j) (r j) ⊆ Ui i) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
