-- Prove2me | Theorems.Thm_PlanarQueue_Planar_planar_has_grid_minor_model
-- name    : PlanarQueue.Planar.planar_has_grid_minor_model
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-29T15:38:40.824036+00:00
-- url     : https://prove2.me/theorems/f08e1878-94f9-4893-b499-2075324a5edb
-- title:
--   Every finite planar graph is a minor of the square grid
-- statement:
--   Let $G$ be a finite graph with a plane drawing. Then $G$ has a *grid minor model* of $G$: finite sets $B_v\subset\mathbb Z^2$ ($v\in V$), pairwise disjoint, nonempty, each connected in the square grid $\mathbb Z^2$, such that adjacent vertices $v\sim w$ have grid-adjacent points $p\in B_v$, $q\in B_w$ (i.e. $G$ is a minor of the infinite square grid):
--
--   $$G \preceq \mathbb Z^2 .$$
--
--   Role: converts the topological planarity hypothesis of Theorem 15 into a combinatorial object (a grid minor model) on which the product-structure construction and the $K_{3,3}$ exclusion are carried out.
--
--   **Formalization Note**: the blob relation and grid adjacency are written out inline (no local definitions); planarity is the platform's `RobertsonSeymour1986.GM5.IsPlanar`.
-- source:
--   N. Robertson and P. D. Seymour, Graph Minors. V. Excluding a planar graph, J. Combin. Theory Ser. B 41 (1986) 92-114, https://doi.org/10.1016/0095-8956(86)90030-4, Section 1 (every planar graph is a minor of a grid), p. 92

import Mathlib
import Definitions.Def_PlanarQueue_Planar_Setting
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

namespace PlanarQueue.Planar

theorem planar_has_grid_minor_model {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsPlanar G) :
    (∃ B : V → Finset (ℤ × ℤ), (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ v, ∀ p ∈ B v, ∀ q ∈ B v, Relation.ReflTransGen (fun a b : ℤ × ℤ => a ∈ B v ∧ b ∈ B v ∧
        (b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨ b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1))) p q) ∧
      (∀ v, (B v).Nonempty) ∧
      (∀ v w, G.Adj v w → ∃ p ∈ B v, ∃ q ∈ B w,
        (q = (p.1 + 1, p.2) ∨ p = (q.1 + 1, q.2) ∨ q = (p.1, p.2 + 1) ∨ p = (q.1, q.2 + 1)))) := by sorry

end PlanarQueue.Planar
