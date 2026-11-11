-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_5_3
-- name    : PlanarDFVSKernel.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:16.27669+00:00
-- url     : https://prove2.me/theorems/5bd45d80-050a-4da5-8160-4b5b2aa3e87d
-- title:
--   Lemma 5.3 — a cut tree for $r\le\rho(J)$ source shores
-- statement:
--   **Lemma 5.3.** Let $J$ be a weakly connected digraph and $1\le r\le\rho(J)$, where $\rho(J)$ is the minimum number of reverses of existing arcs whose addition makes $J$ strongly connected. There exist a directed tree $T$ with $r$ edges and a surjective map $f:V(J)\to V(T)$ such that
--   1. for every arc $u\to v$ of $J$, either $f(u)=f(v)$ or $f(u)\to f(v)$ is an edge of $T$;
--   2. for every edge $e=x\to y$ of $T$, with $C_e$ the component of $T-e$ containing $x$, the set $f^{-1}(C_e)$ is a source shore of $J$;
--   3. all vertices of any strongly connected component of $J$ have the same image under $f$.
--
--   Differences from the source:
--   - encoding: a directed tree T with r edges → a directed tree on the node type Fin (r + 1); reason: a tree with r edges has r + 1 nodes
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 5.3, p.20 (PDF 21)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_DirTree
import Definitions.Def_PlanarDFVSKernel_rho

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Lemma 5.3** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 5.3, p.20 (PDF 21)): "Let J be a weakly connected digraph, and let r
be an integer with 1 ≤ r ≤ ρ(J). There exist a directed tree T with r edges and a surjective map
f : V(J) → V(T) such that: (i) For every arc u → v of J, either f(u) = f(v) or f(u) → f(v) is an
edge of T. (ii) For every edge e = x → y of T, let C_e be the component of the underlying undirected
tree T − e containing x. Then f⁻¹(C_e) is a source shore of J. (iii) All vertices of any strongly
connected component of J have the same image under f."

**Formalization Note** `J` is a multigraph (loops and parallel arcs allowed; the lemma is applied
to `H + Y + P` with parallel copies, p.25 (PDF 26)). A tree with `r` edges has `r + 1` nodes,
so its node type is `Fin (r + 1)`. `ρ(J)` is `rho J`. -/
theorem lemma_5_3 {n m : ℕ} (J : Graph n m) (hJ : WeaklyConnected J) (r : ℕ) (hr1 : 1 ≤ r)
    (hr : r ≤ rho J) :
    ∃ (T : DirTree (Fin (r + 1))) (f : Fin n → Fin (r + 1)), Function.Surjective f ∧
      (∀ e : Fin m, f (J.tail e) = f (J.head e) ∨ T.arc (f (J.tail e)) (f (J.head e))) ∧
      (∀ x y, T.arc x y → IsSourceShore J (f ⁻¹' T.side x y)) ∧
      (∀ u v, SameSCC J u v → f u = f v) := by sorry

end PlanarDFVSKernel
