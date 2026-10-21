-- Prove2me | Theorems.Thm_Tegmark_predictable_m1
-- name    : Tegmark.predictable_m1
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T04:17:16.573553+00:00
-- url     : https://prove2.me/theorems/b396678a-c0ec-4cf8-aedc-1bf5aa9ce149
-- title:
--   Predictability forces exactly one time dimension
-- statement:
--   The predictability prong of the letter (pages L72-L74): a world with the same laws of physics as ours and an (n + m)-dimensional spacetime can contain observers only if the number of time dimensions is m = 1, regardless of the number n of space dimensions. An observer must be able to make at least some predictions: by measuring various nearby field values, to compute field values at more distant spacetime points with non-infinite error bars. This predictability requirement — the field equations are hyperbolic, so that initial-value problems are well posed, and a spacelike hyperplane exists on which to pose the data — holds exactly for the single-time worlds with at least one space dimension. With no time dimension the equations are elliptic and initial-value problems are ill posed: an observer could not make any inferences at all about other parts of space. With two or more time dimensions the equations are ultrahyperbolic, or hyperbolic in the (1, m) tachyon-symmetric cases, but no hypersurface carries well-posed data.
--
--   **Formalization Note** The requirement is the conjunction `hyperbolic class ∧ a spacelike hyperplane ` over the coordinate model; the well-posedness theory behind it (Hadamard, Asgeirsson, via Courant and Hilbert) is the letter's citation and is deliberately represented by the classification, as disclosed in the mission description. The hypothesis n ≥ 1 is the letter's standing setting — a world with observers has at least one space dimension; for n = 0 the requirement already fails at the elliptic clause.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, pp. L72-L74.

import Mathlib
import Definitions.Def_Tegmark_sig
import Definitions.Def_Tegmark_phys
import Definitions.Def_Tegmark_ensemble

namespace Tegmark

/-!
# Predictability forces exactly one time dimension

The predictability prong of Tegmark 1997 (pp. L72-L74): a world with
the same laws of physics as ours and an "(n, m)"-dimensional
spacetime can contain observers only if "m" is 1, regardless of the
number "n" of space dimensions. The requirement is that the field
equations be hyperbolic, so that initial-value problems are well
posed, and that a spacelike hyperplane exist on which to pose the
data. With "m = 0" the equations are elliptic and initial-value
problems are ill posed; with "m" at least 2 there is no spacelike
hyperplane, including the tachyon-symmetric "(1, m)" worlds.
-/

/-- For a world with "n" space dimensions with "n" at least 1 and
"m" time dimensions, the predictability requirement, hyperbolic
field equations together with a spacelike hyperplane on which
initial data can be posed, holds exactly when "m" is 1 (Tegmark
1997, pp. L72-L74). -/
theorem predictable_m1 (n m : ℕ) (_hn : 1 ≤ n) :
    Predictable n m ↔ m = 1 := by
  sorry

end Tegmark
