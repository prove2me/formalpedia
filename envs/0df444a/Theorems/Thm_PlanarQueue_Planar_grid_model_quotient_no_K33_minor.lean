-- Prove2me | Theorems.Thm_PlanarQueue_Planar_grid_model_quotient_no_K33_minor
-- name    : PlanarQueue.Planar.grid_model_quotient_no_K33_minor
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-29T15:39:11.903003+00:00
-- url     : https://prove2.me/theorems/1ad250bd-06a0-495a-9eed-ed67aeeb6f2d
-- title:
--   Quotients of grid minors by connected parts have no $K_{3,3}$ minor
-- statement:
--   Let $G$ be a finite graph with a *grid minor model* of $G$: finite sets $B_v\subset\mathbb Z^2$ ($v\in V$), pairwise disjoint, nonempty, each connected in the square grid $\mathbb Z^2$, such that adjacent vertices $v\sim w$ have grid-adjacent points $p\in B_v$, $q\in B_w$ (i.e. $G$ is a minor of the infinite square grid), and let $\mathcal P$ be a partition of $V(G)$ into parts that each induce a connected subgraph of $G$. Then the quotient $G/\mathcal P$ has no $K_{3,3}$ minor:
--
--   $$K_{3,3}\not\preceq G/\mathcal P .$$
--
--   Role: in the proof of Theorem 15 the quotient $G'/\mathcal P$ of the triangulated supergraph is a minor of $G'$, hence of the grid, so it excludes $K_{3,3}$; with treewidth at most $3$ this makes it planar.
--
--   **Formalization Note**: grid minor model written inline.
-- source:
--   R. Diestel, Graph Theory, 5th ed., Springer GTM 173, 2017, Corollary 4.2.11 ($K_{3,3}$ is not planar) with Proposition 1.7.3 (minor relation is transitive); Dujmović, Joret, Micek, Morin, Ueckerdt, Wood, Planar graphs have bounded queue-number, arXiv:1904.04791v5, https://arxiv.org/abs/1904.04791, proof of Theorem 15, p. 16 ($G/\mathcal P$ is a minor of $G$)

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

namespace PlanarQueue.Planar

theorem grid_model_quotient_no_K33_minor {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : (∃ B : V → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (fun a b : ℤ × ℤ => a ∈ B v ∧ b ∈ B v ∧
        (b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1))) p q) ∧
      (∀ v, (B v).Nonempty) ∧
      (∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w,
        (q = (p.1 + 1, p.2) ∨ p = (q.1 + 1, q.2) ∨ q = (p.1, p.2 + 1) ∨ p = (q.1, q.2 + 1)))))
    (P : Finpartition (Finset.univ : Finset V))
    (hconn : ∀ A ∈ P.parts, (G.induce (A : Set V)).Connected) :
    ¬ RobertsonSeymour1986.GM5.IsMinor (completeBipartiteGraph (Fin 3) (Fin 3)) (quotientGraph G P) := by sorry

end PlanarQueue.Planar
