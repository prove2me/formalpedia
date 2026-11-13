-- Prove2me | Theorems.Thm_StabilityDichotomies_Solvability_monotone_hamming_trajectory
-- name    : StabilityDichotomies.Solvability.monotone_hamming_trajectory
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:58:12.464015+00:00
-- url     : https://prove2.me/theorems/29e3bbaf-54e0-4724-84bf-ee4286fa46b3
-- title:
--   Total Hamming distance along a monotone Boolean trajectory
-- statement:
--   Let $U$ be a finite coordinate set and $x^{(0)},\ldots,x^{(n)}$ Boolean assignments. Suppose that the assignments are coordinatewise nondecreasing on $U$, and every change occurs inside $U$. Then $\sum_{k=0}^{n-1}d_H(x^{(k)},x^{(k+1)})\le |U|$. This is the deterministic Hamming-distance bound used in the monotone-thinning sensitivity argument.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.3, p.17.

import Mathlib
noncomputable section
open scoped Classical BigOperators

namespace StabilityDichotomies.Solvability
theorem monotone_hamming_trajectory {V : Type} [Fintype V]
    (U : Finset V) (n : ℕ) (f : ℕ → V → Bool)
    (hmono : ∀ k < n, ∀ v ∈ U, f k v ≤ f (k + 1) v)
    (hsupport : ∀ k < n, ∀ v ∉ U, f k v = f (k + 1) v) :
    (∑ k ∈ Finset.range n, hammingDist (f k) (f (k + 1))) ≤ U.card := by sorry
end StabilityDichotomies.Solvability
