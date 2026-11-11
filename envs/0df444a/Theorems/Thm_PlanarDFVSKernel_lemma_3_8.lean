-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_3_8
-- name    : PlanarDFVSKernel.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:44.733324+00:00
-- url     : https://prove2.me/theorems/0614e1ae-a002-4232-bcb3-faff3c07fd8f
-- title:
--   Lemma 3.8 — at most $k^2(k+2)$ special vertices, total alternation at most $4k^2(k+2)$
-- statement:
--   **Lemma 3.8.** The number of special vertices and the sum of their alternation counts $\sigma(v)$ are $O(k^3)$.
--
--   Precisely: let $D$ be a loopless plane digraph each of whose weakly connected components is strongly connected and has at least two vertices, and suppose $D$ has $F\le k^2(k+2)$ directed faces (equation (1), the state after Reduction Rule 5). Then
--   $$\bigl|\{v:\sigma(v)>2\}\bigr|\le k^2(k+2),\qquad \sum_{v:\,\sigma(v)>2}\sigma(v)\le 4k^2(k+2).$$
--
--   These bounds control the special groups of the dual instance (Lemma 4.3) and hence the retained set $W$.
--
--   Differences from the source:
--   - generalization: the instance after all of Reduction Rules 1 to 5 → only: loopless, every weakly connected component strongly connected with at least two vertices, F ≤ k²(k + 2); reason: the proof uses only these properties and (1); every reduced instance satisfies them
--   - generalization: O(k³) for both quantities → ≤ k²(k + 2) special vertices and Σ σ(v) ≤ 4k²(k + 2); reason: the explicit bounds |S| ≤ F and Σσ ≤ 4F of the proof (p.14) with (1); they imply O(k³)
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 3.8, p.12 (PDF 13); proof p.12–14 (PDF 13–15); equation (1), p.12 (PDF 13)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_sigma

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Lemma 3.8** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 3.8, p.12 (PDF 13); proof p.12–14 (PDF 13–15), with (1),
p.12 (PDF 13)): "The number of special vertices and the sum of their alternation counts σ(v) are
O(k³)."

Let `D` be a loopless plane digraph each of whose weakly connected components is strongly connected
and has at least two vertices, and suppose it has `F ≤ k²(k + 2)` directed faces (equation (1),
after Reduction Rule 5). Then `D` has at most `k²(k + 2)` special vertices, and their alternation
counts sum to at most `4k²(k + 2)`.

**Formalization Note** The bounds are the explicit ones of the proof (`|S| ≤ F`,
`∑_{v ∈ S} σ(v) ≤ 4F`, p.14 (PDF 15)) combined with (1); they imply `O(k³)`. Only the hypotheses
the proof uses are assumed. Directed faces are the published `circularFaces E`. -/
theorem lemma_3_8 {n m : ℕ} {G : Graph n m} (E : Drawing G) (k : ℕ) (hloop : Loopless G)
    (hscc : ∀ e : Fin m, SameSCC G (G.tail e) (G.head e))
    (hnt : ∀ v : Fin n, ∃ w, w ≠ v ∧ SameSCC G v w)
    (hF : (circularFaces E).card ≤ k ^ 2 * (k + 2)) :
    (specialSet E).card ≤ k ^ 2 * (k + 2) ∧
      ∑ v ∈ specialSet E, sigma E v ≤ 4 * (k ^ 2 * (k + 2)) := by sorry

end PlanarDFVSKernel
