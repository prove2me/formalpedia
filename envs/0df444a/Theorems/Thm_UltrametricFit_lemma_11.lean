-- Prove2me | Theorems.Thm_UltrametricFit_lemma_11
-- name    : UltrametricFit.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:07.825018+00:00
-- url     : https://prove2.me/theorems/091ebfde-3576-4ecb-b739-4a8a83c4a04c
-- title:
--   Lemma 11, p.10 — the approximate inverse Jensen inequality on a biclique
-- statement:
--   Let $d$ be a pseudometric with values in $[0,1]$, $\delta\in(0,1/2)$, and $A,B$ two nodes of the $\delta$-merge forest. Then
--   $$\mathbb E_{i\sim A,\,j\sim B}[\phi(d(i,j))]\ge(1-2\delta)^2\,\phi(d(A,B)).$$
--   This inequality is the main new tool of the analysis: the left side is a lower bound on the average LP cost on the biclique $A\times B$, and the right side depends only on the set distance on which the merge decision is based.
--
--   Differences from the source:
--   - generalization: a metric $d$ → a pseudometric (zero distances between distinct species are allowed); reason: every metric is a pseudometric, and the paper applies the result to the LP layers $x_\ell$, which it calls technically a pseudometric (p.2)
--   - generalization: two nodes of the same δ-merge forest → two sets satisfying the node predicate `IsMergeNode`; reason: every node of a forest satisfies the predicate, so the page's case is included
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Lemma 11, p.10

import Mathlib
import Definitions.Def_UltrametricFit_IsMergeNode

namespace UltrametricFit

/-- **Lemma 11**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), p.10: the
approximate inverse Jensen inequality
`E_{i∼A, j∼B}[φ(d(i, j))] ≥ (1 − 2δ)² φ(d(A, B))` for two nodes `A, B` of the δ-merge forest.

**Formalization Note.** `A, B` are two sets satisfying `IsMergeNode`, which need not lie in one
forest and need not be disjoint. The left side is `avgDist` of the matrix `φ ∘ d`. -/
theorem lemma_11 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsPseudometric d)
    (hd01 : ∀ i j, d i j ∈ Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (A B : Finset (Fin n)) (hA : IsMergeNode d δ A) (hB : IsMergeNode d δ B) :
    (1 - 2 * δ) ^ 2 * phi (avgDist d A B) ≤ avgDist (fun i j => phi (d i j)) A B := by sorry

end UltrametricFit
