-- Prove2me | Theorems.Thm_SP4Gluing_injective_twistedGlueToSphere
-- name    : SP4Gluing.injective_twistedGlueToSphere
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T01:34:11.334347+00:00
-- url     : https://prove2.me/theorems/12c0403c-fdcf-4202-8b53-9f12893b568f
-- title:
--   Injectivity of the twisted gluing map $D^{m+1}\cup_\varphi D^{m+1}\to S^{m+1}$
-- statement:
--   **The glue map from the twisted sphere to the sphere is injective.**
--
--   With two disks glued along their boundaries by $\varphi$, `twistedGlueToSphere` maps the left copy onto the upper hemisphere and the right copy onto the lower one. Injectivity is the statement that no two distinct points of the quotient are identified by that map.
--
--   **Where the content is.** On each copy separately the map is a composition of homeomorphisms, so it is injective there, and the two open hemispheres are disjoint. The whole difficulty is the equator. A point of the left disk's boundary and a point of the right disk's boundary have the same image exactly when they were already identified by the gluing relation `GlueRel`, and checking that requires unwinding: a boundary point $u$ of the left disk maps to the equatorial point determined by $u$, while a boundary point $w$ of the right disk maps through `alexanderExt φ.symm`, which on the boundary sphere is $\varphi^{-1}$ itself (`alexanderExt_sphereToDisk`), and then through the reflected chart. Equality of the two images forces $w = \varphi(u)$ as points of the boundary sphere, which is precisely the relation `GlueRel.glue u`.
--
--   So the statement is the injectivity half of the gluing; combined with surjectivity and continuity it gives the homeomorphism, since the twisted sphere is compact and the target is Hausdorff.
-- source:
--   J. W. Alexander, On the deformation of an n-cell, Proc. Nat. Acad. Sci. USA 9 (1923) 406-407 (the Alexander trick); M. Freedman, The topology of four-dimensional manifolds, J. Diff. Geom. 17 (1982) 357-453. One half of SP4Gluing.twistedSphere_homeomorphic.

import Mathlib
import Definitions.Def_SP4Gluing

set_option autoImplicit false
open Set Metric SP4Gluing

theorem SP4Gluing.injective_twistedGlueToSphere {m : ℕ}
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Function.Injective (twistedGlueToSphere φ) := by sorry
