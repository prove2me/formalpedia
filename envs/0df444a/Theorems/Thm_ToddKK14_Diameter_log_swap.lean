-- Prove2me | Theorems.Thm_ToddKK14_Diameter_log_swap
-- name    : ToddKK14.Diameter.log_swap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:20.265062+00:00
-- url     : https://prove2.me/theorems/a32816fc-1970-436a-b5ef-68576cd2afe0
-- title:
--   §2, p. 2, remark after Theorem 1 — (n − d)^{log₂ d} = d^{log₂(n − d)}
-- statement:
--   Let $d$ and $n$ be natural numbers with $1\le d<n$, and let $\log$ denote the logarithm to base 2. Then
--
--   $$
--   (n-d)^{\log d} \;=\; d^{\log(n-d)} .
--   $$
--
--   Both sides are positive reals whose base-2 logarithm is $\log d\cdot\log(n-d)$. The identity is the symmetry of Todd's bound under linear-programming duality (which swaps $d$ and $n-d$), and the proof of Theorem 1 uses the right-hand form $d^{\log(n-d)}$ in its inductive step.
--
--   **Formalization Note** The powers are real powers (`Real.rpow`) and the logarithms are `Real.logb 2`. The hypothesis $d<n$ keeps both bases positive: at $n=d$ the left side is $0^{\log d}$ and the right side would involve the junk value $\log 0 = 0$ of `Real.logb`.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 2, §2, remark after Theorem 1

import Mathlib

namespace ToddKK14.Diameter

/-- Todd (2014), p. 2, remark after Theorem 1: "(n − d)^{log(d)} = d^{log(n−d)} as both have
logarithm log(d) · log(n − d)", logarithms to base 2, for `1 ≤ d < n`. -/
theorem log_swap (d n : ℕ) (hd : 1 ≤ d) (hdn : d < n) :
    ((n : ℝ) - d) ^ Real.logb 2 d = (d : ℝ) ^ Real.logb 2 ((n : ℝ) - d) := by sorry

end ToddKK14.Diameter
