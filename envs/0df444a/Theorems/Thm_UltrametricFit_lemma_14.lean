-- Prove2me | Theorems.Thm_UltrametricFit_lemma_14
-- name    : UltrametricFit.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:35.623538+00:00
-- url     : https://prove2.me/theorems/d4590a1f-a789-4cb3-a6e1-1bddb40f8a8e
-- title:
--   Lemma 14, p.12 — mistakes on a biclique against the LP cost on one layer
-- statement:
--   Let $x$ be a feasible point of the LP, $\ell\in[L]$, $\delta\in(0,1/2)$, and $A,B$ two disjoint nodes of the $\delta$-merge forest for the metric $x_\ell$. Then:
--
--   1. if $x_\ell(A,B)\le\delta$, then $|E^\ell_-(A,B)|\le\bigl(1+\frac{1}{(1-2\delta)^2}\bigr)\,\mathrm{err}_\ell(A,B)$;
--   2. if $x_\ell(A,B)>\delta$, then $|E^\ell_+(A,B)|\le\bigl(1+\frac{1-\delta}{\delta(1-2\delta)^2}\bigr)\,\mathrm{err}_\ell(A,B)$.
--
--   The first bullet handles pairs the algorithm has merged and the second handles pairs it has refused to merge.
--
--   Differences from the source:
--   - generalization: $x$ an optimal solution of the LP (§3) → $x$ any feasible point; reason: optimal solutions are feasible, so the page's case is included
--   - generalization: two nodes of the same δ-merge forest → two sets satisfying the node predicate `IsMergeNode`; reason: every node of a forest satisfies the predicate, so the page's case is included
--   - encoding: $X, U, x_\ell$ are functions on unordered pairs → symmetric functions on `Fin n × Fin n`, with sums over $i<j$ and diagonals never read; reason: Lean convention; same instances
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Lemma 14, p.12

import Mathlib
import Definitions.Def_UltrametricFit_IsMergeNode
import Definitions.Def_UltrametricFit_IsInstance
import Definitions.Def_UltrametricFit_errLayer

namespace UltrametricFit

/-- **Lemma 14**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), p.12, both
bullets: if `x_ℓ(A, B) ≤ δ` then `|E^ℓ_−(A, B)| ≤ (1 + 1/(1 − 2δ)²) err_ℓ(A, B)`, and if
`x_ℓ(A, B) > δ` then `|E^ℓ_+(A, B)| ≤ (1 + (1 − δ)/(δ(1 − 2δ)²)) err_ℓ(A, B)`.

**Formalization Note.** "Nodes in `T_ℓ`" is `IsMergeNode (x ℓ) δ`, which holds for the forests of a
run by `run_mergeNodes_cover` and also for sets outside any run. `x` is any feasible point, not
only an optimal one. -/
theorem lemma_14 {n : ℕ} (X : Fin n → Fin n → ℝ) (hX : IsInstance X)
    (x : ℕ → Fin n → Fin n → ℝ) (hx : IsFeasible X x) (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (numLayers X))
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (A B : Finset (Fin n))
    (hA : IsMergeNode (x ℓ) δ A) (hB : IsMergeNode (x ℓ) δ B) (hAB : Disjoint A B) :
    (avgDist (x ℓ) A B ≤ δ →
      ((Eminus X ℓ A B).card : ℝ) ≤ (1 + 1 / (1 - 2 * δ) ^ 2) * errLayer X x ℓ A B) ∧
    (δ < avgDist (x ℓ) A B →
      ((Eplus X ℓ A B).card : ℝ) ≤ (1 + (1 - δ) / (δ * (1 - 2 * δ) ^ 2)) * errLayer X x ℓ A B) := by sorry

end UltrametricFit
