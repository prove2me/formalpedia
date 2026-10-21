-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_fact_2_2
-- name    : TreeOrient.RecGreedy.fact_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:26.989448+00:00
-- url     : https://prove2.me/theorems/f39722ff-72d9-46b6-9865-2baebcf756a0
-- title:
--   Fact 2.2 (corrected: rooted edge counts)
-- statement:
--   Let $A$ be a rooted arborescence with at least two edges. There is a vertex $v$ and a partition of $A$ into two edge-disjoint rooted arborescences $A_1,A_2$: $A_1$ is rooted at the original root and contains $v$, while $A_2$ is rooted at $v$. Both parts contain at most two-thirds of the original number of edges:
--
--   $$A_1\cup A_2=A,\qquad 3|A_1|\le 2|A|,\qquad 3|A_2|\le 2|A|.$$
--
--   This separator statement supplies the size reduction used by recursive greedy.
--
--   **Formalization Note** The printed vertex-count version has small-tree counterexamples. The rooted edge-count version is the form used in Lemma 2.5. The correction and its finite checks are recorded in the moderation notes.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 5 (PDF 6), Fact 2.2; corrected rooted edge-count form used in Lemma 2.5, p. 6 (PDF 7)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy

/-- Corrected rooted edge-count form of Fact 2.2, p. 5 (PDF 6). -/
theorem fact_2_2 {n : ℕ} (r : Fin n) (A : Edges n)
    (hA : IsArbo r A) (h2 : 2 ≤ A.card) :
    ∃ v ∈ verts r A, ∃ A₁ A₂ : Edges n,
      Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧ IsArbo r A₁ ∧ v ∈ verts r A₁ ∧
      IsArbo v A₂ ∧ 3 * A₁.card ≤ 2 * A.card ∧ 3 * A₂.card ≤ 2 * A.card := by sorry

end TreeOrient.RecGreedy
