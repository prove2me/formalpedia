-- Prove2me | Theorems.Thm_RovelliLQG_polyhedron_closure
-- name    : RovelliLQG.polyhedron_closure
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T19:27:35.833987+00:00
-- url     : https://prove2.me/theorems/35c7824e-5487-45f2-8ce0-b3eeff086e3a
-- title:
--   Eq. (6): closure — area-weighted outward normals of a polyhedron sum to zero
-- statement:
--   Let $u_1,\dots,u_v\in\mathbb R^3$ be pairwise distinct unit vectors and $h_1,\dots,h_v\in\mathbb R$, and suppose the polyhedron
--   $$P=\{x\in\mathbb R^3:\langle u_l,x\rangle\le h_l,\ l=1,\dots,v\}$$
--   is bounded and has nonempty interior. Write $F_l=P\cap\{\langle u_l,x\rangle=h_l\}$ for its $l$-th face and $A_l$ for the area of $F_l$. Then
--   $$\sum_{l=1}^v A_l\,u_l=0.$$
--
--   This is the classical (Minkowski) relation that the review's gauge-invariance constraint $\sum_{l\in n}\vec L_l=0$ (eq. (6)) mirrors: area-weighted outward normals of a closed polyhedron add up to zero. It is the necessity half of the goal theorem.
--
--   **Formalization Note** Face areas are measured as the Lebesgue measure of the projection onto $u_l^\perp$ and converted to reals; boundedness guarantees they are finite. Faces with $F_l$ empty or degenerate contribute $A_l=0$.
-- source:
--   C. Rovelli, Loop quantum gravity: the first 25 years, Class. Quantum Grav. 28 (2011) 153002, doi:10.1088/0264-9381/28/15/153002, arXiv:1012.4707, §2.1, p. 4, eq. (6) (closure relation; geometric counterpart)

import Mathlib
import Definitions.Def_RovelliLQG_Defs

open scoped InnerProductSpace

namespace RovelliLQG

theorem polyhedron_closure {v : ℕ} (u : Fin v → E3) (hu : ∀ l, ‖u l‖ = 1)
    (hinj : Function.Injective u) (h : Fin v → ℝ)
    (hbdd : Bornology.IsBounded (halfspacePolyhedron u h))
    (hint : (interior (halfspacePolyhedron u h)).Nonempty) :
    ∑ l, (planarArea (u l) (polyhedronFace u h l)).toReal • u l = 0 := by
  sorry

end RovelliLQG
