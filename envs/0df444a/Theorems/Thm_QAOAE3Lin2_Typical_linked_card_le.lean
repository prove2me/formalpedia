-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_linked_card_le
-- name    : QAOAE3Lin2.Typical.linked_card_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:02.09516+00:00
-- url     : https://prove2.me/theorems/c294525b-57cf-4d3f-839d-7f1d87a4737d
-- title:
--   Section III, p. 11, after (57) — each equation is linked to at most (6D + 3)(D + 1) equations
-- statement:
--   Let the triples form an E3LIN2 family in which every bit lies in at most $D+1$ equations. Call two equations **linked** when their dependency sets (the $d$'s appearing in (25) for each of them) intersect. Then every equation $abc$ is linked to at most
--   $$(6D+3)(D+1)$$
--   equations, itself included.
--
--   Summed over the $m$ equations, at most $m(6D+3)(D+1)$ pairs contribute to the variance of (55).
--
--   **Formalization Note** "Linked" is defined through the $d$'s of (25), which is what (57) requires; the paper's count goes through the at most $6D+3$ bits involved in the $abc$ factor of (56).
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 11, Section III, after (57)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- p. 11: each equation is "linked" (shares a sign `d` of (25)) with at most `(6D + 3)(D + 1)`
equations, itself included. -/
theorem linked_card_le {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (D : ℕ)
    (htri : QAOAE3Lin2.General.IsTripleFamily tri) (hocc : QAOAE3Lin2.General.BoundedOccurrence tri D) (i : Fin m) :
    (Finset.univ.filter fun i' => ¬ Disjoint (deps tri i) (deps tri i')).card ≤
      (6 * D + 3) * (D + 1) := by sorry

end QAOAE3Lin2.Typical
