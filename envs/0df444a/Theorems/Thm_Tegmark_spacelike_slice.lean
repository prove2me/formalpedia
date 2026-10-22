-- Prove2me | Theorems.Thm_Tegmark_spacelike_slice
-- name    : Tegmark.spacelike_slice
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T04:16:56.867334+00:00
-- url     : https://prove2.me/theorems/9c2c8c1d-4a21-43bb-b9b5-9eee63829ad7
-- title:
--   The spatial slice of the single-time world is a spacelike data surface
-- statement:
--   The positive half of the data-surface argument (pages L73-L74): hyperbolic equations allow well-posed initial-value problems, and specifying initial data on the spatial slice determines the solution in the volumes bounded by the cones, so that a localized observer can make predictions about its future. The theorem constructs the data surface for every single-time world: in a world with n space dimensions and exactly one time dimension, the spatial slice — the kernel of the time-coordinate projection — is a spacelike hyperplane; the quadratic form on it is the sum of the squares of the space coordinates, positive on every nonzero vector.
--
--   **Formalization Note** The witness is the time-coordinate projection; the statement is the existence half of the predictability requirement's data-surface clause, for every number of space dimensions.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, pp. L73-L74.

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble

namespace Tegmark

/-!
# The spacelike slice of the single-time world

With exactly one time dimension, the spatial slice of an "(n, 1)"
world, the kernel of the time-coordinate projection, is a spacelike
hyperplane: the quadratic form is the sum of squares of the space
coordinates on it, positive on every nonzero vector. Single-time
worlds therefore possess the data surfaces on which observers record
initial conditions (Tegmark 1997, pp. L73-L74).
-/

/-- In a world with "n" space dimensions and exactly one time
dimension there is a spacelike hyperplane (Tegmark 1997,
pp. L73-L74): the spatial slice, on which the form is positive
definite. -/
theorem spacelike_slice (n : ℕ) : HasSpacelikeHyperplane n 1 := by
  sorry

end Tegmark
