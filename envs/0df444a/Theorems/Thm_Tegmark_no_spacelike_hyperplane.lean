-- Prove2me | Theorems.Thm_Tegmark_no_spacelike_hyperplane
-- name    : Tegmark.no_spacelike_hyperplane
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T04:16:13.020639+00:00
-- url     : https://prove2.me/theorems/7e3827ed-4fc9-4d63-bb87-808ec5a02486
-- title:
--   No spacelike data surfaces in worlds with two or more time dimensions
-- statement:
--   The linear-algebra core of the letter's Asgeirsson discussion (page L74): in the ultrahyperbolic case there are no spacelike and no timelike hypersurfaces, and hence no well-posed initial-value problems, since a hypersurface by definition has a dimensionality one less than the spacetime manifold. The theorem states the hyperplane obstruction: when the number m of time dimensions is at least two, no hyperplane of the point space — the kernel of a nonzero linear functional — is spacelike; the kernel must meet the time block in a nonzero purely timelike vector, on which the form is negative, so the kernel cannot be positive definite. And when the number n of space dimensions is at least two, no hyperplane is timelike, by the same argument with the two blocks exchanged. This is what destroys every data surface of the multi-time worlds, including the (1, m) tachyon-symmetric ones that the classification places in the hyperbolic class.
--
--   **Formalization Note** A hyperplane is the kernel of a nonzero linear functional; spacelike means the quadratic form is positive on every nonzero vector of the kernel, timelike that it is negative. The letter's deeper Asgeirsson phenomenon (data in an effectively one-dimensional cylinder determining the solution in a higher-dimensional region, the free-lunch symptom of ill-posedness) is out of scope; the obstruction is the part of the discussion that is linear algebra.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, p. L74 (after Asgeirsson 1936; Courant and Hilbert 1962).

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble

namespace Tegmark

/-!
# No spacelike data surfaces in multi-time worlds

The linear-algebra core of the Asgeirsson discussion of Tegmark 1997
(p. L74): in the ultrahyperbolic case there are no spacelike and no
timelike hypersurfaces, hence no well-posed initial-value problems.
A hyperplane is the kernel of a nonzero linear functional; when there
are at least two time dimensions, such a kernel must meet the time
block in a nonzero purely timelike vector, so it cannot be positive
definite; and when there are at least two space dimensions, it must
meet the space block in a nonzero purely spacelike vector, so it
cannot be negative definite.
-/

/-- With at least two time dimensions no hyperplane of the point
space is spacelike, and with at least two space dimensions no
hyperplane is timelike (Tegmark 1997, p. L74): a codimension-one
subspace cannot be positive definite when m is at least 2, and
cannot be negative definite when n is at least 2. -/
theorem no_spacelike_hyperplane (n m : ℕ) :
    (2 ≤ m → ¬ HasSpacelikeHyperplane n m) ∧
    (2 ≤ n → ¬ HasTimelikeHyperplane n m) := by
  sorry

end Tegmark
