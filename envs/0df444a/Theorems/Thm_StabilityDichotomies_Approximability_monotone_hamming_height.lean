-- Prove2me | Theorems.Thm_StabilityDichotomies_Approximability_monotone_hamming_height
-- name    : StabilityDichotomies.Approximability.monotone_hamming_height
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:03:20.464754+00:00
-- url     : https://prove2.me/theorems/c15a4f8e-7a52-49e5-af4a-350118239ed4
-- title:
--   Hamming distance equals potential difference along a monotone Boolean pair
-- statement:
--   If two Boolean assignments x and y on a finite variable set satisfy x ≤ y coordinatewise, then their Hamming distance equals the number of ones in y minus the number of ones in x. This identity relates the coupled output distance to the potential difference used in the sensitivity proof of Theorem 4.3.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, proof of Theorem 4.3, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem StabilityDichotomies.Approximability.monotone_hamming_height {V : Type} [Fintype V] (x y : V → Bool) (hxy : x ≤ y) :
    (hammingDist x y : ℝ) =
      (∑ v : V, if y v then (1 : ℝ) else 0) - ∑ v : V, if x v then (1 : ℝ) else 0 := by sorry
