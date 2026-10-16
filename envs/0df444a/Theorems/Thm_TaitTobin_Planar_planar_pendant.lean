-- Prove2me | Theorems.Thm_TaitTobin_Planar_planar_pendant
-- name    : TaitTobin.Planar.planar_pendant
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-15T12:27:59.738666+00:00
-- url     : https://prove2.me/theorems/8c706f2b-8a79-47c3-ae92-0e2f69b8e561
-- title:
--   Joining an isolated vertex to one other vertex preserves planarity (used in the proof of Lemma 10, p. 9)
-- statement:
--   Let $G$ be a planar graph on $n$ vertices, let $u$ be a vertex of $G$ with no neighbours, and let $a\neq u$ be another vertex. Let $G'$ be the graph on the same vertex set whose edges are the edges of $G$ together with the single edge $ua$. Then $G'$ is planar:
--   $$G \text{ planar},\ \deg_G(u)=0,\ a\ne u \ \Longrightarrow\ G+ua \text{ planar}.$$
--
--   Role: in the proof of Lemma 10, all edges at a vertex $z$ of the extremal planar graph are deleted and $z$ is joined to the vertex $x$ of largest eigenvector entry; this fact says the resulting graph is again planar, so that maximality of the spectral radius can be compared with it.
--
--   **Formalization Note**: Planarity is the published `IsPlanar` (a crossing-free arc drawing). The vertex $u$ is isolated in $G$ (it may be placed anywhere in the plane). `G'` is described by its adjacency relation; it is the graph $G+ua$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, https://arxiv.org/abs/1606.01916, p. 9, proof of Lemma 10 (the graph obtained by removing the edges at z and joining z to x is planar)

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open RobertsonSeymour1986.GM5

theorem planar_pendant {n : ℕ} (G : SimpleGraph (Fin n)) (hG : IsPlanar G)
    (u a : Fin n) (hua : u ≠ a) (hu : ∀ q, ¬ G.Adj u q)
    (G' : SimpleGraph (Fin n))
    (hG' : ∀ p q, G'.Adj p q ↔
      (G.Adj p q ∨ (p = u ∧ q = a) ∨ (q = u ∧ p = a))) :
    IsPlanar G' := by sorry

end TaitTobin.Planar
