-- Prove2me | Theorems.Thm_TaitTobin_Planar_planar_attach_to_edge
-- name    : TaitTobin.Planar.planar_attach_to_edge
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-15T14:53:50.579965+00:00
-- url     : https://prove2.me/theorems/70453657-69f8-4d3e-9465-4a687ae10f18
-- title:
--   Joining an isolated vertex to both ends of an edge preserves planarity (used in the proof of Lemma 14, p. 12)
-- statement:
--   Let $G$ be a planar graph on $n$ vertices, let $ab$ be an edge of $G$, and let $u$ be a vertex of $G$ with no neighbours. Let $G'$ be the graph on the same vertex set whose edges are the edges of $G$ together with $ua$ and $ub$. Then $G'$ is planar:
--   $$G \text{ planar},\ ab\in E(G),\ \deg_G(u)=0 \ \Longrightarrow\ G+ua+ub \text{ planar}.$$
--
--   Role: in the proof of Lemma 14, a vertex of the extremal planar graph is detached from its neighbours and joined to the two hubs $x\sim w$; this fact says the resulting graph is again planar, so that maximality of the spectral radius can be compared with it.
--
--   **Formalization Note**: Planarity is the published `IsPlanar` (a crossing-free arc drawing). The vertex $u$ is isolated in $G$ (it may be placed anywhere in the plane), so $u\ne a$ and $u\ne b$ follow from $ab\in E(G)$. `G'` is described by its adjacency relation; it is the graph $G+ua+ub$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, https://arxiv.org/abs/1606.01916, p. 12, proof of Lemma 14 (the graph obtained by joining a vertex to x and w, which are adjacent, is planar)

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open RobertsonSeymour1986.GM5

theorem planar_attach_to_edge {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (a b u : Fin n) (hab : G.Adj a b) (hu : ∀ q, ¬ G.Adj u q)
    (G' : SimpleGraph (Fin n))
    (hG' : ∀ p q, G'.Adj p q ↔
      (G.Adj p q ∨ (p = u ∧ (q = a ∨ q = b)) ∨ (q = u ∧ (p = a ∨ p = b)))) :
    IsPlanar G' := by sorry

end TaitTobin.Planar
