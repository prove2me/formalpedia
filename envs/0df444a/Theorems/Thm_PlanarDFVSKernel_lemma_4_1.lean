-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_4_1
-- name    : PlanarDFVSKernel.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:47.813147+00:00
-- url     : https://prove2.me/theorems/c65fde06-6950-4b3c-9e4b-3fc58b1bb637
-- title:
--   Lemma 4.1 — $D-X$ is acyclic iff $H+\bigcup_{u\in X}R_u$ is strongly connected
-- statement:
--   **Lemma 4.1.** Let $D$ be a strongly connected loopless plane digraph, $H$ its directed dual, and for each vertex $u$ let $R_u$ be the group of reversals of the boundary arcs of the dual face $F_u$ (the dual arcs of the arcs at $u$). For every $X\subseteq V(D)$, the graph $D-X$ is acyclic if and only if adding to $H$ the groups $R_u$, $u\in X$, makes $H$ strongly connected.
--
--   This is the translation of vertex deletion into arc augmentation via planar cycle–cut duality.
--
--   Differences from the source:
--   - generalization: the reduced instance D (after §3), strongly connected → any strongly connected loopless plane digraph; reason: the proof uses only strong connectivity, looplessness and the embedding
--   - encoding: dual vertices = faces; dual arc from the right-hand face to the left-hand face → published dart orbits; dualArc e from faceOf (e, true) to faceOf (e, false); reason: the same dual; the statement is invariant under reversing all dual arcs and groups together
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 4.1, p.15 (PDF 16); setting §4.1, p.14 (PDF 15)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_dualArc

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Lemma 4.1** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 4.1, p.15 (PDF 16), in the setting of §4.1, p.14 (PDF 15):
"First suppose that D is strongly connected. Construct its directed dual H […] For each u ∈ V(D),
let R_u be the group containing the reversals of all boundary arcs of F_u."): "For every X ⊆ V(D),
the graph D − X is acyclic if and only if adding to H the groups associated with X makes H strongly
connected."

Let `D` be a strongly connected loopless plane digraph, `H` its directed dual (vertices: the faces;
one arc per arc of `D`, from its right-hand to its left-hand face) and `R_u` the reversals of the
dual arcs of the arcs at `u`. For every vertex set `X`, `D − X` is acyclic if and only if every
face can reach every face using the arcs of `H` and of the groups `R_u`, `u ∈ X`.

**Formalization Note** "Acyclic" is the published `InducedAcyclic G (univ ∖ X)`. The statement is
invariant under reversing all dual arcs (and with them all groups), so it does not depend on the
right/left convention of `dualArc`. -/
theorem lemma_4_1 {n m : ℕ} {G : Graph n m} (E : Drawing G) (hsc : StronglyConnected G)
    (hloop : Loopless G) (X : Finset (Fin n)) :
    InducedAcyclic G (Finset.univ \ X) ↔
      ∀ f g : Face E, Relation.ReflTransGen
        (fun a b => (a, b) ∈ dualArcs E ∨ ∃ u ∈ X, (a, b) ∈ vertexGroup E u) f g := by sorry

end PlanarDFVSKernel
