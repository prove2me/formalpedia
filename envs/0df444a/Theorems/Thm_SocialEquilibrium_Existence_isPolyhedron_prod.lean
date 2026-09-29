-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_isPolyhedron_prod
-- name    : SocialEquilibrium.Existence.isPolyhedron_prod
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:40:10.876472+00:00
-- url     : https://prove2.me/theorems/988627d2-6735-4fe8-89f1-f738212d2d17
-- title:
--   §1 — the product of two polyhedra is a polyhedron
-- statement:
--   Let $E$ and $F$ be finite-dimensional real normed spaces. If $P\subseteq E$ and $Q\subseteq F$ are polyhedra (sets homeomorphic to geometric polyhedra), then
--   $$P\times Q\subseteq E\times F$$
--   is a polyhedron: it is homeomorphic to the product of the two geometric antecedents.
--
--   Together with the product of contractible sets, this makes the set of action profiles of the existence theorem a contractible polyhedron.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 887, §1 Topological Concepts (product of two polyhedra, last sentence)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §1, p. 887: the product of two polyhedra is a polyhedron. -/
theorem isPolyhedron_prod {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) :
    IsPolyhedron (P ×ˢ Q) := by sorry

end SocialEquilibrium.Existence
