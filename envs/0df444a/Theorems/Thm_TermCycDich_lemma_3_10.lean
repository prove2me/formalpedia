-- Prove2me | Theorems.Thm_TermCycDich_lemma_3_10
-- name    : TermCycDich.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:34.002921+00:00
-- url     : https://prove2.me/theorems/6443d711-084f-4a99-8f2d-af59309e59e0
-- title:
--   Lemma 3.10 — local rerouting in a terminal-free $(4\times3)$-mesh
-- statement:
--   Let $(G,T)$ be an annotated graph and let $C$ be a $T$-cycle in $G$. Let $M$ be a $(4\times3)$-mesh with horizontal paths $P_1,\dots,P_4$ and vertical paths $Q_1,Q_2,Q_3$ such that
--
--   $$
--   C\cap M=Q_1\cup Q_2\cup Q_3\qquad\text{and}\qquad V(M)\cap T=\emptyset .
--   $$
--
--   Then there is a $T$-cycle $C'$ with
--
--   $$
--   V(C')\cap V(Q_2)\cap V(P_2)=\emptyset\qquad\text{and}\qquad V(C')\cap\bigl(V(G)\setminus V(M)\bigr)=V(C)\cap\bigl(V(G)\setminus V(M)\bigr).
--   $$
--
--   The lemma lets a solution crossing a terminal-free mesh along its three vertical paths be rerouted inside the mesh; it is used to reduce the number of crossings of an annulus.
--
--   **Formalization Note** $C\cap M=Q_1\cup Q_2\cup Q_3$ is an equality of subgraphs (vertices and edges). Indices are 0-based in Lean ($P_2$ is `P 1`, $Q_2$ is `Q 1`).
--
--   Differences from the source:
--   - reading: the intersection P_i ∩ Q_j induces a path (mesh definition) → the common subgraph P_i ⊓ Q_j (common vertices and edges) is a path; reason: the meaning drawn in Figure 9 (shared purple edges); a reading by induced subgraphs of G would not make the intersection a subpath of Q_j, which the proof uses
--   - encoding: paths, the mesh M = P_1 ∪ … ∪ Q_3 and the cycle C → subgraphs traced by path walks, M = (⨆ i, P i) ⊔ (⨆ j, Q j), C a closed walk with IsCycle, 0-based indices; reason: Lean convention; same instances
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Lemma 3.10, p.28 (PDF 30); meshes p.17 (PDF 19)

import Mathlib
import Definitions.Def_TermCycDich_IsRCycle
import Definitions.Def_TermCycDich_IsMesh

namespace TermCycDich

/-- **Lemma 3.10 (local rerouting lemma).** Let `C` be a `T`-cycle of `G` and `M` a terminal-free
`(4 × 3)`-mesh with paths `P_1, …, P_4, Q_1, Q_2, Q_3` such that `C ∩ M = Q_1 ∪ Q_2 ∪ Q_3`. Then
some `T`-cycle `C'` avoids `V(Q_2) ∩ V(P_2)` and agrees with `C` outside `V(M)`.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Lemma 3.10, p.28 (PDF 30).

**Formalization Note** Indices are 0-based: `P_2` is `P 1`, `Q_2` is `Q 1`. The mesh is
`IsMesh (n := 2) (m := 1)` (sizes `2 + 2 = 4` and `1 + 2 = 3`), its graph is
`M = (⨆ i, P i) ⊔ (⨆ j, Q j)`. `C ∩ M = Q_1 ∪ Q_2 ∪ Q_3` is an equality of subgraphs (vertices and
edges): `C.toSubgraph ⊓ M = ⨆ j, Q j`. The conclusion is about vertex sets. -/
theorem lemma_3_10 {V : Type} [Fintype V] (G : SimpleGraph V) (T : Set V) {u : V}
    (C : G.Walk u u) (hC : IsRCycle G T C) (P : Fin 4 → G.Subgraph) (Q : Fin 3 → G.Subgraph)
    (hM : IsMesh (n := 2) (m := 1) P Q)
    (hCM : C.toSubgraph ⊓ ((⨆ i, P i) ⊔ (⨆ j, Q j)) = ⨆ j, Q j)
    (hT : Disjoint ((⨆ i, P i) ⊔ (⨆ j, Q j)).verts T) :
    ∃ (u' : V) (C' : G.Walk u' u'), IsRCycle G T C' ∧
      (∀ x ∈ C'.support, x ∈ (Q 1).verts → x ∉ (P 1).verts) ∧
      ∀ x, x ∉ ((⨆ i, P i) ⊔ (⨆ j, Q j)).verts → (x ∈ C'.support ↔ x ∈ C.support) := by sorry

end TermCycDich
