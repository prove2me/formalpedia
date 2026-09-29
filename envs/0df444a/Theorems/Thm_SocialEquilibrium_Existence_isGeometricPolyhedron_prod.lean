-- Prove2me | Theorems.Thm_SocialEquilibrium_Existence_isGeometricPolyhedron_prod
-- name    : SocialEquilibrium.Existence.isGeometricPolyhedron_prod
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:39:32.968491+00:00
-- url     : https://prove2.me/theorems/9308c323-c56d-4dc7-aecd-5f5e09dc72a1
-- title:
--   §1 — the product of two geometric polyhedra is a geometric polyhedron
-- statement:
--   Let $E$ and $F$ be finite-dimensional real vector spaces. If $P\subseteq E$ and $Q\subseteq F$ are geometric polyhedra (finite unions of convex cells), then
--   $$P\times Q\subseteq E\times F$$
--   is a geometric polyhedron.
--
--   This is used to show that products of polyhedra are polyhedra.
-- source:
--   Debreu, A Social Equilibrium Existence Theorem, Proc. Natl. Acad. Sci. USA 38(10), 1952, p. 887, §1 Topological Concepts (product of two geometric polyhedra)

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsPolyhedron

namespace SocialEquilibrium.Existence

/-- Debreu (1952), §1, p. 887: the product of two geometric polyhedra is a geometric
polyhedron. -/
theorem isGeometricPolyhedron_prod {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {Q : Set F} (hP : IsGeometricPolyhedron P) (hQ : IsGeometricPolyhedron Q) :
    IsGeometricPolyhedron (P ×ˢ Q) := by sorry

end SocialEquilibrium.Existence
