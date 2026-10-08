-- Prove2me | Theorems.Thm_ProjSchedTW_OrderPolyhedra_feasible_region_eq_union_minimal_order_polyhedra
-- name    : ProjSchedTW.OrderPolyhedra.feasible_region_eq_union_minimal_order_polyhedra
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T15:30:34.471217+00:00
-- url     : https://prove2.me/theorems/e930e855-eee7-4a0d-abaf-26ce1ae2facb
-- title:
--   Theorem 2.3.7 — the feasible region is the union of the order polyhedra of the minimal feasible strict orders
-- statement:
--   Consider a project satisfying the standing assumptions. Let $\mathcal O$ be the set of all inclusion-minimal feasible strict orders in $V$, i.e. feasible strict orders $O$ such that no feasible strict order $O'$ satisfies $O' \subsetneq O$. Then $\mathcal O$ is finite and
--   $$\mathcal S = \bigcup_{O \in \mathcal O} \mathcal S_T(O).$$
--
--   This is the basic structural theorem of Bartusch et al. (1988): the feasible region, in general neither convex nor connected, is a finite union of polyhedra.
--
--   **Formalization Note** Minimality is Mathlib's `Minimal` for the predicate "is a feasible strict order", ordered by inclusion, so the minimum is taken among feasible strict orders only. Finiteness is automatic since $V$ is finite.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 32, Theorem 2.3.7

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders

namespace ProjSchedTW.OrderPolyhedra

/-- Theorem 2.3.7 (p. 32), the basic structural theorem: let `𝒪` be the (finite) set of all
inclusion-minimal feasible strict orders in `V`. Then the feasible region is
`𝒮 = ⋃_{O ∈ 𝒪} S_T(O)`. -/
theorem feasible_region_eq_union_minimal_order_polyhedra {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) :
    {O : Finset (Fin (n + 2) × Fin (n + 2)) | Minimal P.IsFeasibleOrder O}.Finite ∧
    {S : Fin (n + 2) → ℝ | P.IsFeasible S} =
      ⋃ O ∈ {O : Finset (Fin (n + 2) × Fin (n + 2)) | Minimal P.IsFeasibleOrder O},
        P.orderPolyhedron O := by sorry

end ProjSchedTW.OrderPolyhedra
