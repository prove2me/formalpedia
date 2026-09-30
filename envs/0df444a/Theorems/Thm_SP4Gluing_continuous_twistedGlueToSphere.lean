-- Prove2me | Theorems.Thm_SP4Gluing_continuous_twistedGlueToSphere
-- name    : SP4Gluing.continuous_twistedGlueToSphere
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T01:33:52.665971+00:00
-- url     : https://prove2.me/theorems/e09b0118-b3a4-44e3-9ba2-e70fb31a2faa
-- title:
--   Continuity of the twisted gluing map $D^{m+1}\cup_\varphi D^{m+1}\to S^{m+1}$
-- statement:
--   **The glue map from the twisted sphere to the sphere is continuous.**
--
--   Two copies of the closed disk $D^{m+1}$ are glued along their boundary spheres by a homeomorphism $\varphi$, and `twistedGlueToSphere` sends the resulting quotient to $S^{m+1}$: the left copy goes to the upper hemisphere by the chart `upperHemisphereHomeoDisk`, the right copy to the lower hemisphere by `lowerHemisphereHomeoDiskRefl` after applying the Alexander extension of $\varphi^{-1}$. The map is already constructed in the definition bundle, with its well-definedness on the quotient discharged; what is claimed here is continuity.
--
--   **Why it is not free.** A map out of a `Quot` is continuous exactly when its composite with the quotient projection is, and that composite is `Sum.elim` of the two branch maps. The first branch is a composition of homeomorphisms and is continuous outright. The second is not: it factors through `alexanderExt φ.symm`, defined by
--   $$w \;\longmapsto\; \|w\|\cdot \varphi^{-1}\!\left(\frac{w}{\|w\|}\right),$$
--   which is a quotient by $\|w\|$ and so has no continuity at the centre of the disk for formal reasons. Continuity there holds because $\bigl\|\,\|w\|\cdot\varphi^{-1}(w/\|w\|)\bigr\| = \|w\|$ exactly — the radial factor annihilates the discontinuity of the direction $w/\|w\|$ — so the map is squeezed to $0$ as $w\to0$. Away from the centre the direction map `unitOr` is continuous on $\{w \ne 0\}$, which is open, and the rest is composition.
--
--   Mathlib has neither the Alexander trick nor any radial-extension API, so this has to be built from `continuousOn_unitOr` in the mission's own chart bundle together with a squeeze at the origin.
-- source:
--   J. W. Alexander, On the deformation of an n-cell, Proc. Nat. Acad. Sci. USA 9 (1923) 406-407 (the Alexander trick); M. Freedman, The topology of four-dimensional manifolds, J. Diff. Geom. 17 (1982) 357-453. One half of SP4Gluing.twistedSphere_homeomorphic.

import Mathlib
import Definitions.Def_SP4Gluing

set_option autoImplicit false
open Set Metric SP4Gluing

theorem SP4Gluing.continuous_twistedGlueToSphere {m : ℕ}
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Continuous (twistedGlueToSphere φ) := by sorry
