-- Prove2me | Theorems.Thm_StrictCQ_AGP_projection_nonexpansive
-- name    : StrictCQ.AGP.projection_nonexpansive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:37:28.259236+00:00
-- url     : https://prove2.me/theorems/92c1d575-b464-4b8b-9302-8b7f5ca9c8f7
-- title:
--   (4.10), proof of Theorem 4.2, p. 8 — the Euclidean projection onto a closed convex set is nonexpansive
-- statement:
--   Let $S\subset\mathbb R^n$ be a nonempty, closed, convex set. If $y$ is the Euclidean projection of $z$ onto $S$ and $y'$ is the Euclidean projection of $z'$ onto $S$, then
--
--   $$
--   \|y-y'\|\le\|z-z'\|.
--   $$
--
--   The proof of Theorem 4.2 uses this non expansivity in (4.10) to compare the projection of $x^k+\omega^*$ with that of $\omega^k+y^k$.
--
--   **Formalization Note** Projections are given as points satisfying the projection predicate rather than as values of a function.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 8, (4.10), proof of Theorem 4.2

import Mathlib
import Definitions.Def_StrictCQ_AGP_Setting

open Filter Topology InnerProductSpace

namespace StrictCQ.AGP

/-- (4.10): the Euclidean projection onto a nonempty closed convex set is nonexpansive. -/
theorem projection_nonexpansive {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hne : S.Nonempty) (hcl : IsClosed S) (hcv : Convex ℝ S)
    (z z' y y' : EuclideanSpace ℝ (Fin n)) (hy : IsProj S z y) (hy' : IsProj S z' y') :
    ‖y - y'‖ ≤ ‖z - z'‖ := by sorry

end StrictCQ.AGP
