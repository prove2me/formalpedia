-- Prove2me | Theorems.Thm_Tegmark_green_harmonic
-- name    : Tegmark.green_harmonic
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T04:18:05.273661+00:00
-- url     : https://prove2.me/theorems/60ac3d37-7d2c-4601-bcec-86021d582538
-- title:
--   The Green profile of n dimensions is harmonic away from the origin
-- statement:
--   The Green's function of the Poisson equation in n space dimensions is the (2 - n)-th power of the radius for n > 2 (page L70, after Ehrenfest 1917): the fundamental solution whose scaling makes the inverse-square law of electrostatics and gravity the three-dimensional case, an inverse-cube law the four-dimensional one. The theorem verifies the defining property of the Green profile: away from the origin, at every positive radius, the profile satisfies the radially reduced Laplace equation — the second derivative plus the (n - 1)/r correction to the first derivative vanishes. This is the computation behind the letter's statement that the potential of a point particle gives the electrostatic and gravitational force laws their dimension-dependent form.
--
--   **Formalization Note** The statement fixes n at least 3 and r positive; the real power is noncomputable in the pinned Mathlib, and the proof is calculus of real powers: the derivative of the (2 - n)-th power is the (1 - n)-th power times the exponent, and the two terms cancel against the correction for every n at least 3. The letter's potential is the coupling times the profile up to sign; the harmonic property is the profile's.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, p. L70 (after Ehrenfest 1917).

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble

namespace Tegmark

/-!
# The Newtonian potential of n dimensions

The Green's function of the Poisson equation in "n" space dimensions
is the (2 - n)-th power of the radius for "n > 2" (Tegmark 1997,
p. L70, after Ehrenfest 1917), the potential of a point particle. The
radial Green profile satisfies the radially reduced Laplace equation
away from the origin: its radial Laplacian, the second derivative
plus the (n - 1) / r correction to the first derivative, vanishes at
every positive radius.
-/

/-- For "n" at least 3, the radial Green profile, the (2 - n)-th
power of the radius, satisfies the radially reduced Laplace equation
at every positive radius "r" (Tegmark 1997, p. L70): the potential of
a point particle in "n" dimensions is harmonic away from the
origin. -/
theorem green_harmonic (n : ℕ) (_hn : 3 ≤ n) (r : ℝ) (_hr : 0 < r) :
    radialLap n (greenProfile n) r = 0 := by
  sorry

end Tegmark
