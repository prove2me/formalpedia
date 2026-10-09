-- Prove2me | Theorems.Thm_PlanarQueue_Genus_lemma_21
-- name    : PlanarQueue.Genus.lemma_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:22:23.571302+00:00
-- url     : https://prove2.me/theorems/e1368385-6d51-4194-a35d-cc4f34c81038
-- title:
--   Lemma 21 — cutting a connected Z with at most 2g vertices per BFS layer leaves a planar graph inside a planar G⁺ with the same layers
-- statement:
--   Let $G$ be a connected finite graph of Euler genus at most $g$, let $T$ be a BFS spanning tree of $G$ rooted at $r$, and let $V_i = \{v : \operatorname{dist}_G(r, v) = i\}$ be the corresponding BFS layering. Then there is a subgraph $Z \subseteq G$ such that
--
--   1. $Z$ is connected or empty, and $|V(Z) \cap V_i| \le 2g$ for every $i \ge 0$;
--   2. $G - V(Z)$ is planar;
--   3. there are a connected finite planar graph $G^+$ containing $G - V(Z)$ as a subgraph, a vertex $r^+$ of $G^+$ and a BFS spanning tree $T^+$ of $G^+$ rooted at $r^+$, whose BFS layering $W_i = \{w : \operatorname{dist}_{G^+}(r^+, w) = i\}$ satisfies
--   $$W_i \cap \bigl(V(G) \setminus V(Z)\bigr) = V_i \setminus V(Z) \qquad (i \ge 0);$$
--   4. for every vertical path $P$ in $T^+$, the set $P \cap (V(G) \setminus V(Z))$ is empty or is the vertex set of a vertical path in $T$.
--
--   The lemma reduces graphs of bounded Euler genus to planar graphs at the price of a set $Z$ that is thin in every BFS layer. In the proof of Theorem 2 it is combined with Lemma 18 applied to $G^+$.
--
--   **Formalization Note** "Euler genus $g$" is read as "Euler genus at most $g$" (`EulerGenusLE`); the bound $2g$ is monotone in $g$, so nothing is lost. $G^+$ is a graph on its own finite vertex type, and $G - V(Z)$ sits inside it through an injective map $\iota$ preserving adjacency; condition 3's layer identity is stated as $\operatorname{dist}_{G^+}(r^+, \iota(a)) = \operatorname{dist}_G(r, a)$ for every $a \notin V(Z)$. The paper says "$Z$ is connected" and its proof takes $Z = \emptyset$ when $g = 0$; since Mathlib's connectedness requires a vertex, the statement reads "empty or connected". Likewise the intersection in 4 may be empty (e.g. when $P$ lies in the added part of $G^+$), so it reads "empty or a vertical path". Planarity is the published plane-drawing predicate `RobertsonSeymour1986.GM5.IsPlanar`, while Euler genus is the combinatorial embedding-scheme notion; "Euler genus $0$ implies planar" is used implicitly by the paper at $g = 0$ and is part of what a proof must supply.
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, p. 19, Lemma 21 (proof pp. 19–22)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_PlanarQueue_Genus_Setting
import Definitions.Def_PlanarQueue_Genus_EulerGenus

namespace PlanarQueue.Genus

/-- Lemma 21 (p. 19). The layer of `v` in the BFS layering of `T` is `G.dist r v`. The planar graph
`G⁺` lives on a finite type `W`, and `G − V(Z)` sits inside it through the embedding `ι`. -/
theorem lemma_21 (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (g : ℕ) (hg : EulerGenusLE G g)
    (T : SimpleGraph V) (r : V) (hT : IsBFSTree G T r) :
    ∃ Z : G.Subgraph,
      (Z.verts = ∅ ∨ Z.Connected) ∧
      (∀ i : ℕ, Nat.card {v : V // v ∈ Z.verts ∧ G.dist r v = i} ≤ 2 * g) ∧
      RobertsonSeymour1986.GM5.IsPlanar (G.induce Z.vertsᶜ) ∧
      ∃ (W : Type) (_ : Finite W) (Gp Tp : SimpleGraph W) (rp : W) (ι : ↥(Z.vertsᶜ) ↪ W),
        Gp.Connected ∧ RobertsonSeymour1986.GM5.IsPlanar Gp ∧
        (∀ a b : ↥(Z.vertsᶜ), G.Adj a b → Gp.Adj (ι a) (ι b)) ∧
        IsBFSTree Gp Tp rp ∧
        (∀ a : ↥(Z.vertsᶜ), Gp.dist rp (ι a) = G.dist r a) ∧
        ∀ l : List W, IsVertical Tp rp l →
          {v : V | ∃ h : v ∈ Z.vertsᶜ, ι ⟨v, h⟩ ∈ l} = ∅ ∨
            IsVerticalSet T r {v : V | ∃ h : v ∈ Z.vertsᶜ, ι ⟨v, h⟩ ∈ l} := by sorry

end PlanarQueue.Genus
