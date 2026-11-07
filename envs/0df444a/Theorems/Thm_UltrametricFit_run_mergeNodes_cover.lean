-- Prove2me | Theorems.Thm_UltrametricFit_run_mergeNodes_cover
-- name    : UltrametricFit.run_mergeNodes_cover
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:24.4992+00:00
-- url     : https://prove2.me/theorems/86b1dd73-31c5-44b8-a47f-fd3ba51db892
-- title:
--   §4.3, p.11 and proof of Theorem 1, p.15 — the merge forests of a run, and the covering of pairs
-- statement:
--   Let $x$ be feasible, $\delta\in(0,1/2)$, and consider a run of Merge($\delta$) on $x$. Then:
--
--   1. the clusters of each $C_\ell$, $0\le\ell\le L$, are non-empty and partition the species;
--   2. for each $\ell\in[L]$, each cluster of $C_{\ell-1}$ and each cluster of $C_\ell$ is a node of a $\delta$-merge forest for the metric $x_\ell$ (the paper's "$T_{\ell-1}$ is a $\delta$-merge forest on layer $\ell$");
--   3. for each merge event $(\ell^*,A,B)$: $\ell^*\in[L]$, the sets $A,B$ are disjoint, $x_{\ell^*}(A,B)\le\delta$, and $A,B$ are nodes for the metric $x_\ell$ for each $\ell\ge\ell^*$ in $[L]$;
--   4. each pair $i\ne j$ is covered by exactly one merge event;
--   5. if a merge event $(\ell^*,A,B)$ covers the pair $i,j$, then each output has $U(i,j)=D_{\ell^*}$.
--
--   This is the decomposition of the cost of the algorithm into edge-disjoint bicliques.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of the LP (§3) → $x$ any feasible point; reason: optimal solutions are feasible, so the page's case is included
--   - encoding: Algorithm 1 with unspecified merge order → a relation `IsRun` with a universal quantifier over runs, and a relational output `IsOutput`; reason: the paper fixes no order (and §5 speaks of the worst one), so every order is an execution of the algorithm
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
--   - encoding: a node $(A\cup B,\ell^*)$ of the final forest $T_L$ → a merge event $(\ell^*,A,B)$ in the list `mergeEvents` of a run; reason: the nodes of $T_L$ other than leaves are exactly the merges of the run; the forest is not a separate object
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), §4.3, p.11; proof of Theorem 1, p.15

import Mathlib
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_IsFeasible
import Definitions.Def_UltrametricFit_IsMergeNode
import Definitions.Def_UltrametricFit_IsRun

namespace UltrametricFit

/-- **The merge forests `T_ℓ` of a run, and the covering claim**, Charikar, Gao, STOC 2027 submission
(manuscript sha256 87af12a2…), §4.3, p.11 and proof of Theorem 1, p.15. For a run on a feasible
`x`: clusters are non-empty and partition the species; each cluster of `C_{ℓ−1}` and of `C_ℓ`, and
each side of a merge event of a layer `≤ ℓ`, is a node for the metric `x_ℓ` ("T_{ℓ−1} is a δ-merge
forest on layer ℓ"); the two sides of an event are disjoint with `x_{ℓ*}(A, B) ≤ δ`; each pair
`i ≠ j` is covered by exactly one event; and an output takes the value `D_{ℓ*}` on the pairs covered
by the event `(ℓ*, A, B)`.

**Formalization Note.** `List.countP … = 1` counts events with multiplicity, so "exactly once" also
excludes a repeated event. -/
theorem run_mergeNodes_cover {n : ℕ} (X : Fin n → Fin n → ℝ) (hX : IsInstance X)
    (x : ℕ → Fin n → Fin n → ℝ) (hx : IsFeasible X x) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (C : ℕ → Finset (Finset (Fin n))) (M : ℕ → List (Finset (Fin n) × Finset (Fin n)))
    (hrun : IsRun X x δ C M) :
    (∀ ℓ, ℓ ≤ numLayers X → ∀ A ∈ C ℓ, A.Nonempty) ∧
    (∀ ℓ, ℓ ≤ numLayers X → ∀ i, ∃! A, A ∈ C ℓ ∧ i ∈ A) ∧
    (∀ ℓ ∈ Finset.Icc 1 (numLayers X),
      (∀ A ∈ C (ℓ - 1), IsMergeNode (x ℓ) δ A) ∧ (∀ A ∈ C ℓ, IsMergeNode (x ℓ) δ A)) ∧
    (∀ e ∈ mergeEvents X M,
      e.1 ∈ Finset.Icc 1 (numLayers X) ∧ Disjoint e.2.1 e.2.2 ∧ avgDist (x e.1) e.2.1 e.2.2 ≤ δ ∧
      ∀ ℓ, e.1 ≤ ℓ → ℓ ≤ numLayers X →
        IsMergeNode (x ℓ) δ e.2.1 ∧ IsMergeNode (x ℓ) δ e.2.2) ∧
    (∀ i j, i ≠ j → (mergeEvents X M).countP (covers i j) = 1) ∧
    (∀ e ∈ mergeEvents X M, ∀ i j, covers i j e = true →
      ∀ U, IsOutput X C U → U i j = layerValue X e.1) := by sorry

end UltrametricFit
