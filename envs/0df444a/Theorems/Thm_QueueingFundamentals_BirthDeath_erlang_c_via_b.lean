-- Prove2me | Theorems.Thm_QueueingFundamentals_BirthDeath_erlang_c_via_b
-- name    : QueueingFundamentals.BirthDeath.erlang_c_via_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T07:17:28.061129+00:00
-- url     : https://prove2.me/theorems/7bb38cca-4774-494d-9e6d-3f31ba478db0
-- title:
--   Eq. (2.55) — the Erlang-C formula through the Erlang-B formula
-- statement:
--   Let $c$ be a number of servers and $r$ an offered load with $0 < r < c$. Then the Erlang-C formula (2.38) and the Erlang-B formula (2.53) are related by
--   $$C(c, r) = \frac{c\,B(c, r)}{c - r + r\,B(c, r)}.$$
--
--   Combined with the recursion (2.54), this computes the $M/M/c$ probability of delay stably, and it links the delay system to the loss system with the same number of servers.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, p.83, Eq. (2.55)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang

namespace QueueingFundamentals.BirthDeath

/-- Eq. (2.55), p.83. For `c` servers and offered load `0 < r < c`, the Erlang-C formula is a
function of the Erlang-B formula: `C(c, r) = c B(c, r) / (c − r + r B(c, r))`. -/
theorem erlang_c_via_b (c : ℕ) (r : ℝ) (hr : 0 < r) (hrc : r < c) :
    erlangC c r = (c : ℝ) * erlangB c r / ((c : ℝ) - r + r * erlangB c r) := by sorry

end QueueingFundamentals.BirthDeath
