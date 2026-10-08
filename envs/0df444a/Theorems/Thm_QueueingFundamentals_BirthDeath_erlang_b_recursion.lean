-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_erlang_b_recursion
-- name    : QueueingFundamentals.BirthDeath.erlang_b_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:17:36.377046+00:00
-- url     : https://prove2.me/theorems/eb5a218e-ed77-419a-b5db-522e6617b2be
-- title:
--   Eq. (2.54) — the Erlang-B recursion
-- statement:
--   Let $r > 0$ and let $B(c, r)$ be the Erlang-B formula. Then $B(0, r) = 1$ and, for every $c \ge 1$,
--   $$B(c, r) = \frac{r\,B(c-1, r)}{c + r\,B(c-1, r)}.$$
--
--   The recursion computes $B(c, r)$ without the factorials of (2.53), which overflow in floating point for large $c$.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.82, Eq. (2.54)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

namespace QueueingFundamentals.BirthDeath

/-- Eq. (2.54), p.82. For an offered load `r > 0`, the Erlang-B formula satisfies
`B(c, r) = r B(c − 1, r) / (c + r B(c − 1, r))` for `c ≥ 1`, with `B(0, r) = 1`. -/
theorem erlang_b_recursion (r : ℝ) (hr : 0 < r) :
    erlangB 0 r = 1 ∧
      ∀ c : ℕ, 1 ≤ c →
        erlangB c r = r * erlangB (c - 1) r / ((c : ℝ) + r * erlangB (c - 1) r) := by sorry

end QueueingFundamentals.BirthDeath
