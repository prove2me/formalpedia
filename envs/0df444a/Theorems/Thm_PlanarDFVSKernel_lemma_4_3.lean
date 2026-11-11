-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_4_3
-- name    : PlanarDFVSKernel.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:37:11.718556+00:00
-- url     : https://prove2.me/theorems/00467341-ef9d-4f3b-b424-a06f388904e8
-- title:
--   Lemma 4.3 — the groups after Reduction Rule 6
-- statement:
--   **Lemma 4.3.** After applying Reduction Rule 6 the dual instance has the following properties. Let $D$ be a loopless plane digraph each of whose weakly connected components is strongly connected with at least two vertices, with $F\le k^2(k+2)$ directed faces, let $H$ be its directed dual and let the group of each vertex be as produced by Rule 6.
--   1. Every ordinary group ($\sigma(u)=2$) contains exactly one arc. The group of a special vertex $v$ contains at most $\sigma(v)$ arcs, and the special groups contain at most $4k^2(k+2)$ arcs in total.
--   2. For every base arc $u\to v$ (the dual arc of an arc $e$), some group contains a reverse arc $t\to s$ whose directed boundary path is $s\rightsquigarrow u\to v\rightsquigarrow t$: the run of arc ends containing an end of $e$ produces $t\to s$, and its dual arcs lead from $s$ to $u$ and from $v$ to $t$.
--   3. Adding all groups makes every weakly connected component of $H$ strongly connected.
--
--   Differences from the source:
--   - generalization: the instance after Reduction Rules 1–5 and 6 → only: loopless, every weakly connected component strongly connected with at least two vertices, F ≤ k²(k + 2); reason: the proof uses only these (and Lemma 3.8)
--   - generalization: total number of arcs in special groups O(k³) → ≤ 4k²(k + 2); reason: Lemma 3.8's explicit bound with |group(v)| ≤ σ(v); implies O(k³)
--   - reading: adding all groups makes H strongly connected → every weakly connected component of H becomes strongly connected; reason: H is the disjoint union of the component duals (p.17), and the proof argues per component ("Since H is weakly connected")
--   - encoding: the corresponding directed boundary path s ⇝ u → v ⇝ t → a run (p, d) at an endpoint of e containing e's arc end, its reverse arc runArc p d in the group, and walks along the run's dual arcs from s to the dual tail and from the dual head to t; reason: the boundary path of a run consists of the dual arcs of its arc ends
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 4.3, p.16 (PDF 17)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_ArcReach
import Definitions.Def_PlanarDFVSKernel_sigma
import Definitions.Def_PlanarDFVSKernel_dualArc
import Definitions.Def_PlanarDFVSKernel_rule6Group

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Lemma 4.3** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 4.3, p.16 (PDF 17)): "After applying Reduction Rule 6, the instance
has the following properties. (i) Every ordinary group contains one arc. The group associated with a
special vertex v contains at most σ(v) arcs, and the total number of arcs in special groups is
O(k³). (ii) For every base arc u → v, at least one group contains a reverse arc t → s whose
corresponding directed boundary path is s ⇝ u → v ⇝ t. Adding all groups makes H strongly
connected."

Under the hypotheses of Lemma 3.8 (loopless, every weakly connected component strongly connected with
at least two vertices, `F ≤ k²(k + 2)` directed faces), with `H` the directed dual and the groups
of Reduction Rule 6:
1. the group of every ordinary vertex (`σ(u) = 2`) has exactly one arc;
2. the group of every special vertex `v` has at most `σ(v)` arcs;
3. the special groups have at most `4k²(k + 2)` arcs in total;
4. for every arc `e` there are a vertex `u` and a run of arc ends at `u` containing the end of
   `e` at `u`, whose reverse arc `t → s` lies in the group of `u` and whose directed boundary
   path (the dual arcs of the run) leads from `s` to the tail of the dual arc of `e` and from its
   head to `t`;
5. adding all groups makes every weakly connected component of `H` strongly connected.

**Formalization Note** "Ordinary group" is the group of a vertex with `σ = 2`; the total
`O(k³)` is the explicit `4k²(k + 2)` given by Lemma 3.8 and (1). "Makes H strongly connected" is
read per weakly connected component of `H` (`H` is the disjoint union of the component duals,
p.17 (PDF 18)). -/
theorem lemma_4_3 {n m : ℕ} {G : Graph n m} (E : Drawing G) (k : ℕ) (hloop : Loopless G)
    (hscc : ∀ e : Fin m, SameSCC G (G.tail e) (G.head e))
    (hnt : ∀ v : Fin n, ∃ w, w ≠ v ∧ SameSCC G v w)
    (hF : (circularFaces E).card ≤ k ^ 2 * (k + 2)) :
    ((∀ u : Fin n, sigma E u = 2 → (rule6Group E u).card = 1) ∧
      (∀ u ∈ specialSet E, (rule6Group E u).card ≤ sigma E u) ∧
      ∑ u ∈ specialSet E, (rule6Group E u).card ≤ 4 * (k ^ 2 * (k + 2))) ∧
    ((∀ e : Fin m, ∃ (u : Fin n) (p d : Dart m), IsRunAt E u p d ∧
        (∃ b : Bool, origin G (e, b) = u ∧ InRun E p d (e, b)) ∧
        runArc E p d ∈ rule6Group E u ∧
        Relation.ReflTransGen (runPathArc E p d) (runArc E p d).2 (dualArc E e).1 ∧
        Relation.ReflTransGen (runPathArc E p d) (dualArc E e).2 (runArc E p d).1) ∧
      ∀ f g : Face E, ArcWeakReach (dualArcs E) f g →
        Relation.ReflTransGen
          (fun a b => (a, b) ∈ dualArcs E ∨ ∃ u, (a, b) ∈ rule6Group E u) f g) := by sorry

end PlanarDFVSKernel
