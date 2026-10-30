-- Prove2me | Theorems.Thm_PlanarQueue_Planar_theorem_15_core_grid_model
-- name    : PlanarQueue.Planar.theorem_15_core_grid_model
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-29T15:40:33.161308+00:00
-- url     : https://prove2.me/theorems/b9e25c3a-db62-46f1-8872-cbf8bbe5f657
-- title:
--   Theorem 15 core: tripod partition of a grid-minor supergraph
-- statement:
--   Let $G$ be a finite graph with a *grid minor model* of $G$: finite sets $B_v\subset\mathbb Z^2$ ($v\in V$), pairwise disjoint, nonempty, each connected in the square grid $\mathbb Z^2$, such that adjacent vertices $v\sim w$ have grid-adjacent points $p\in B_v$, $q\in B_w$ (i.e. $G$ is a minor of the infinite square grid), and let $L$ be a BFS layering of $G$. Then there are a supergraph $G'\supseteq G$ on the same vertex set that again has a grid minor model, and a partition $\mathcal P$ of $V$ into parts inducing connected subgraphs of $G'$, such that every part meets every layer in at most three vertices and
--
--   $$\operatorname{tw}(G'/\mathcal P)\le 3 .$$
--
--   Role: this is the combinatorial heart of Theorem 15 (the tripod decomposition of a triangulation, Lemma 16); the parent transfers width and treewidth from $G'/\mathcal P$ to $G/\mathcal P$ and gets planarity of the quotient from the sibling children.
--
--   **Formalization Note**: planarity is replaced by an inline grid minor model of $G$ and of the supergraph $G'$ (the triangulation of the paper).
-- source:
--   Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, https://arxiv.org/abs/1904.04791, Lemma 16 and the proof of Theorem 15, p. 16-17

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

namespace PlanarQueue.Planar

theorem theorem_15_core_grid_model {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : (∃ B : V → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (fun a b : ℤ × ℤ => a ∈ B v ∧ b ∈ B v ∧
        (b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1))) p q) ∧
      (∀ v, (B v).Nonempty) ∧
      (∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w,
        (q = (p.1 + 1, p.2) ∨ p = (q.1 + 1, q.2) ∨ q = (p.1, p.2 + 1) ∨ p = (q.1, q.2 + 1)))))
    (L : V → ℕ) (hL : IsBFSLayering G L) :
    ∃ (G' : SimpleGraph V) (P : Finpartition (Finset.univ : Finset V)),
      G ≤ G' ∧
    (∃ B : V → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (fun a b : ℤ × ℤ => a ∈ B v ∧ b ∈ B v ∧
        (b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1))) p q) ∧
      (∀ v, (B v).Nonempty) ∧
      (∀ v w, G'.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w,
        (q = (p.1 + 1, p.2) ∨ p = (q.1 + 1, q.2) ∨ q = (p.1, p.2 + 1) ∨ p = (q.1, q.2 + 1)))) ∧
      (∀ A ∈ P.parts, (G'.induce (A : Set V)).Connected) ∧
      (∀ A ∈ P.parts, ∀ i : ℕ, (A.filter fun v => L v = i).card ≤ 3) ∧
      RobertsonSeymour1986.GM5.TreewidthLE (quotientGraph G' P) 3 := by sorry

end PlanarQueue.Planar
