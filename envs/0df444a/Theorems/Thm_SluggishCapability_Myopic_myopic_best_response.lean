-- Prove2me | Theorems.Thm_SluggishCapability_Myopic_myopic_best_response
-- name    : SluggishCapability.Myopic.myopic_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:05:29.066763+00:00
-- url     : https://prove2.me/theorems/18cafb01-c2e1-43ed-9446-11f9609d54d3
-- title:
--   (2), p. 8 — the myopic rule is the unique cost-minimizing sluggish choice
-- statement:
--   Let $c \in (0,1)$ and let $m, d \ge 0$ be integers: $m$ is last period's capability and $d$ the current challenge. The feasible choices are the non-negative integers $m' \in \{m-1, m, m+1\}$, and choosing $m'$ costs $C(m') = c\, m' + \max(0, d - m')$. Let $g(m,d)$ be the myopic update (2): $m+1$ if $d > m$, $m$ if $d = m$, and $\max\{0, m-1\}$ if $d < m$. Then $g(m, d)$ is feasible and
--   $$C(g(m,d)) < C(m') \quad \text{for every feasible } m' \ne g(m,d).$$
--
--   This is the paper's observation that a myopic agent minimizing the current cost follows (2); it ties the cost model of §2 to the adjustment rule assumed in Proposition 1.
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), p. 8, eq. (2), with the cost C_t of p. 7

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_SluggishCapability_Myopic_Setting

open MarkovMixing

namespace SluggishCapability.Myopic

/-- Rule (2), p. 8: with `c ∈ (0, 1)`, the myopic update `myopicStep m d` is a feasible sluggish
choice (in `{m − 1, m, m + 1} ∩ ℕ`) and is the unique minimizer of the period cost
`C = c·m' + max(0, d − m')` over the feasible choices `m'`. -/
theorem myopic_best_response (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (m d : ℕ) :
    (myopicStep m d + 1 = m ∨ myopicStep m d = m ∨ myopicStep m d = m + 1) ∧
    ∀ m' : ℕ, (m' + 1 = m ∨ m' = m ∨ m' = m + 1) → m' ≠ myopicStep m d →
      periodCost c (myopicStep m d) d < periodCost c m' d := by sorry

end SluggishCapability.Myopic
