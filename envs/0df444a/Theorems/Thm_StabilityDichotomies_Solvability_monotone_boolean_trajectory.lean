-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_monotone_boolean_trajectory
-- name    : StabilityDichotomies.Solvability.monotone_boolean_trajectory
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:56:26.398932+00:00
-- url     : https://prove2.me/theorems/ba1e17b8-4284-4925-8186-90cde241dd60
-- title:
--   Monotone Boolean trajectories flip each coordinate at most once
-- statement:
--   Let $U$ be a finite set of coordinates, and let $x^{(0)},\ldots,x^{(n)}$ be Boolean assignments that are coordinatewise nondecreasing on $U$. The total number of coordinate changes on $U$ along the trajectory is at most $|U|$. This is the finite monotone-trajectory bound underlying the sensitivity analysis of Theorem 4.3; it does not assert the theorem’s derivative identity or Wasserstein estimate.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.17.

import Mathlib
noncomputable section
open scoped Classical BigOperators

namespace StabilityDichotomies.Solvability
theorem monotone_boolean_trajectory {V : Type} [Fintype V]
    (U : Finset V) (n : ℕ) (f : ℕ → V → Bool)
    (hmono : ∀ k < n, ∀ v ∈ U, f k v ≤ f (k + 1) v) :
    (∑ k ∈ Finset.range n, ∑ v ∈ U,
      (if f k v ≠ f (k + 1) v then (1 : ℤ) else 0)) ≤ U.card := by sorry
end StabilityDichotomies.Solvability
