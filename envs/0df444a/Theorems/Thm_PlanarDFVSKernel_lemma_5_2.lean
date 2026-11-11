-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_5_2
-- name    : PlanarDFVSKernel.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:21.480906+00:00
-- url     : https://prove2.me/theorems/ecf9435c-b199-4ff4-ad73-8ddec7d8072a
-- title:
--   Lemma 5.2 — $O((|W|(k+1)+1)^4)$ truncated distance records
-- statement:
--   **Lemma 5.2.** In a planar digraph with arc lengths zero or one, fix a vertex set $W$ and $k\in\mathbb N$. The distance record of a vertex $v$ is $\bigl(\min\{d(a,v),k+1\}\bigr)_{a\in W}$. The number of distinct records, over all vertices $v$, is $O((|W|(k+1)+1)^4)$, with an absolute constant.
--
--   Applied to the auxiliary graph $L$ of §5.1, it bounds the number of vertices after Reduction Rule 7.
--
--   Differences from the source:
--   - encoding: O((|W|(k + 1) + 1)⁴) → c·(|W|(k + 1) + 1)⁴ with c chosen before the graph, W and k; reason: the O(·) is uniform
--   - encoding: arc lengths zero or one; records as tuples (θ₁, …, θ_|W|) → lengths ℓ : arcs → ℕ with ℓ ≤ 1; records as functions on W; reason: the same records
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 5.2, p.19 (PDF 20)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_dist

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp
open scoped NNReal ENNReal

open Classical in
/-- **Lemma 5.2** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 5.2, p.19 (PDF 20)): "In a planar digraph with arc lengths zero or
one, fix a vertex set W. Form each vertex's distance record using distances from the vertices of W,
truncated at k + 1. The number of distinct records is O((|W|(k + 1) + 1)⁴)."

There is a constant `c` such that for every planar digraph with arc lengths in `{0, 1}`, every
vertex set `W` and every `k`, the records `v ↦ (min{d(a, v), k + 1})_{a ∈ W}`, over all vertices
`v`, take at most `c (|W|(k + 1) + 1)⁴` distinct values.

**Formalization Note** Distances are `dist` with the lengths cast to `ℝ≥0`; truncation at
`k + 1` maps `∞` to `k + 1`. The record is indexed by `W` itself. The constant is universal. -/
theorem lemma_5_2 :
    ∃ c : ℕ, ∀ (n m : ℕ) (G : Graph n m), Planar G → ∀ (ℓ : Fin m → ℕ), (∀ e, ℓ e ≤ 1) →
      ∀ (W : Finset (Fin n)) (k : ℕ),
        (Finset.univ.image fun v : Fin n => fun a : W =>
            min (dist G (fun e => (ℓ e : ℝ≥0)) (a : Fin n) v) ((k + 1 : ℕ) : ℝ≥0∞)).card ≤
          c * (W.card * (k + 1) + 1) ^ 4 := by sorry

end PlanarDFVSKernel
