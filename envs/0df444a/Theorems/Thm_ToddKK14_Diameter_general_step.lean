-- Prove2me | Theorems.Thm_ToddKK14_Diameter_general_step
-- name    : ToddKK14.Diameter.general_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:35.844316+00:00
-- url     : https://prove2.me/theorems/bcd9b614-1790-4a90-930c-319ba29309da
-- title:
--   §2, p. 3, proof of Theorem 1, displayed chain — the corrected general power inequality
-- statement:
--   Let $d$ and $n$ be natural numbers with $d\ge 4$, $n-d\ge 8$ and $n\ge 2d$, and let $\log$ be the logarithm to base 2. Then
--
--   $$
--   (d-1)^{\log(n-d)} + 2\cdot (n/2-d)^{\log d} + 2 \;\le\; d^{\log(n-d)} .
--   $$
--
--   This is the analytic content of the displayed chain in the general inductive step of the proof of Theorem 1, from its second line to its last. In the proof, the first line of the chain is Lemma 1, $\Delta(d,n)\le\Delta(d-1,n-1)+2\Delta(d,\lfloor n/2\rfloor)+2$, and the passage to the second line inserts the induction hypotheses $\Delta(d-1,n-1)\le (d-1)^{\log(n-d)}$ and $\Delta(d,\lfloor n/2\rfloor)\le (\lfloor n/2\rfloor-d)^{\log d}$; those steps belong to the proof of the goal theorem, not to this statement.
--
--   **Formalization Note** Powers are real powers and logarithms are `Real.logb 2`; $n/2$ is real division. The hypothesis $n\ge 2d$ is a disclosed addition: in the paper it holds because the case $n<2d$ was dispatched earlier, and it is needed for Lemma 1 ($d\le\lfloor n/2\rfloor$). For $n>2d$, the second power equals the paper's $d^{\log(n/2-d)}$ by the log-swap identity. At $n=2d$, the printed logarithm is undefined; $(n/2-d)^{\log d}=0$ states the zero contribution from $\Delta(d,d)=0$ and avoids Lean's junk value $d^{\operatorname{logb}_2 0}=1$.
-- source:
--   Todd, An improved Kalai-Kleitman bound for the diameter of a polyhedron, arXiv:1402.3579v2, p. 3, §2, proof of Theorem 1, displayed chain for the case d ≥ 4, n − d ≥ 8

import Mathlib

namespace ToddKK14.Diameter

/-- Todd (2014), p. 3, proof of Theorem 1, the displayed chain for `d ≥ 4`, `n − d ≥ 8` (with
`2d ≤ n`, the case `n < 2d` having been dispatched before). The second summand uses
`(n/2-d)^{log d}`, equal to the printed `d^{log(n/2-d)}` when `n > 2d` and equal to zero when
`n = 2d`, where the printed logarithm is undefined. All logarithms are to base 2. -/
theorem general_step (d n : ℕ) (hd : 4 ≤ d) (hnd : d + 8 ≤ n) (h2d : 2 * d ≤ n) :
    ((d : ℝ) - 1) ^ Real.logb 2 ((n : ℝ) - d) + 2 * (((n : ℝ) / 2 - d) ^ Real.logb 2 d) + 2
      ≤ (d : ℝ) ^ Real.logb 2 ((n : ℝ) - d) := by sorry

end ToddKK14.Diameter
