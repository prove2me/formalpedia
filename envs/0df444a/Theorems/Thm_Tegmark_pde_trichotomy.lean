-- Prove2me | Theorems.Thm_Tegmark_pde_trichotomy
-- name    : Tegmark.pde_trichotomy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T04:14:56.688457+00:00
-- url     : https://prove2.me/theorems/ee55eac0-8633-4aa0-b6f6-e948612e19eb
-- title:
--   The trichotomy of the field equations: elliptic, hyperbolic, ultrahyperbolic
-- statement:
--   The classification of the covariant field equations of an (n, m)-dimensional world by the signs of the eigenvalues of the principal symbol (pages L72-L73). For the wave equation and the Klein-Gordon equation the principal symbol has the same eigenvalue signs as the metric, so the class of the field equations is completely determined by the numbers of space and time dimensions: elliptic exactly when there are no space or no time dimensions (all eigenvalues share a sign, the signature (+ + + +) of the letter); hyperbolic exactly when there is at least one dimension of each kind and exactly one of one kind (one eigenvalue against the rest, the signature (+ - - -) of the letter); ultrahyperbolic exactly when there are at least two of each (the signature (+ + - -) of the letter). The theorem states the three equivalences as a conjunction.
--
--   **Formalization Note** The statement is the unfolding of the classifier `pdeClass`, which encodes the letter's classification as a function of the pair (n, m); it is the entry milestone of the mission, calibrating the definitions before the milestones with genuine logical content.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, pp. L72-L73.

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble

namespace Tegmark

/-!
# The trichotomy of the field equations

The classification of the covariant field equations of an "(n, m)"
world by the eigenvalue signs of the principal symbol (Tegmark 1997,
pp. L72-L73): the class is completely determined by the numbers of
space and time dimensions. Elliptic means that all eigenvalues share
a sign, that is, there are no space or no time dimensions; hyperbolic
means that exactly one eigenvalue has one sign and the rest the
other, that is, at least one dimension of each kind and exactly one
of one kind; ultrahyperbolic means at least two eigenvalues of each
sign.
-/

/-- The trichotomy of the field equations (Tegmark 1997,
pp. L72-L73): for a world with "n" space and "m" time dimensions, the
field equations are elliptic exactly when there are no space or no
time dimensions, hyperbolic exactly when there is at least one
dimension of each kind and exactly one of one kind, and
ultrahyperbolic exactly when there are at least two of each. -/
theorem pde_trichotomy (n m : ℕ) :
    (pdeClass n m = PDEClass.elliptic ↔ n = 0 ∨ m = 0) ∧
    (pdeClass n m = PDEClass.hyperbolic ↔ n ≠ 0 ∧ m ≠ 0 ∧ (n = 1 ∨ m = 1)) ∧
    (pdeClass n m = PDEClass.ultrahyperbolic ↔ 2 ≤ n ∧ 2 ≤ m) := by
  sorry

end Tegmark
