-- Prove2me | Theorems.Thm_Tegmark_orbit_stability_31
-- name    : Tegmark.orbit_stability_31
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T04:18:49.676885+00:00
-- url     : https://prove2.me/theorems/cdf78074-c2a2-4f60-9b9b-50a19dd18897
-- title:
--   Stable circular orbits exist exactly in three space dimensions
-- statement:
--   The stability prong of the letter (pages L70-L71): neither classical atoms nor planetary orbits can be stable in a space with more than three dimensions (Ehrenfest 1917), and the two-body problem no longer has stable orbit solutions — the light particles of the letter's figure 2 that approach the heavy one either escape to infinity or get sucked into a cataclysmic collision, and there are no stable orbits. The theorem states the dichotomy for the Newtonian two-body problem in the effective-potential form: for n at least 3, a space of n dimensions admits stable circular orbits exactly when n is 3. At a circular orbit the curvature of the effective potential is the product of the coupling, (n - 2), (4 - n), and a power of the radius: positive only for n = 3, zero for the spiralling n = 4 of the letter's figure, and negative beyond.
--
--   **Formalization Note** A stable circular orbit is a positive critical point of the effective potential — the centrifugal barrier plus the Newtonian potential — with positive curvature there, the linear stability of the orbit; the existence predicate quantifies over positive coupling, angular momentum, and radius. The letter's quantum claim (the hydrogen atom has no bound states for n > 3, Tangherlini 1963) is the quantum counterpart and is out of scope, as disclosed in the mission description.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, pp. L70-L71 (after Ehrenfest 1917; citing Tangherlini 1963 and Buechel 1963).

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble

namespace Tegmark

/-!
# Stable orbits exist exactly in three space dimensions

The stability prong of Tegmark 1997 (pp. L70-L71): for "n" at least
3, the Newtonian two-body problem in "n" space dimensions has stable
circular orbits exactly when "n" is 3. At a circular orbit the
curvature of the effective potential is the product of "k", "(n - 2)",
"(4 - n)", and the (2 - n)-th power of the radius: positive only for
"n = 3", zero for the spiralling "n = 4" case of the letter's
figure 2, and negative beyond. For "n > 3" there are no stable
orbits and no stable atoms, so such worlds cannot contain stable
observers.
-/

/-- For a space of "n" dimensions with "n" at least 3, the
Newtonian two-body problem admits stable circular orbits exactly
when "n" is 3 (Tegmark 1997, pp. L70-L71). -/
theorem orbit_stability_31 (n : ℕ) (_hn : 3 ≤ n) :
    HasStableOrbit n ↔ n = 3 := by
  sorry

end Tegmark
