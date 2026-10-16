-- Prove2me | Theorems.Thm_SecretaryAdvice_BinaryLimit_thresholds_ordered
-- name    : SecretaryAdvice.BinaryLimit.thresholds_ordered
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T00:43:25.200422+00:00
-- url     : https://prove2.me/theorems/5bbc5034-69fd-41d2-a903-0a9ad74f3a99
-- title:
--   Theorem 20, p. 20 — Y threshold precedes N threshold
-- statement:
--   For $n\ge1$ and $p,p'\in[1/2,1]$, the first positive $Y$ coordinate of the rescaled greedy dual occurs no later than the first positive $N$ coordinate:
--
--   $$t_Y(n,p,p')\le t_N(n,p,p').$$
--
--   The order is the finite threshold relation asserted in Theorem 20. A value $n+1$ means that the corresponding signal is never accepted.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, p. 20, Theorem 20, first sentence

import Mathlib
import Definitions.Def_SecretaryAdvice_BinaryLimit_Dual

namespace SecretaryAdvice.BinaryLimit

theorem thresholds_ordered (n : ℕ) (p pp : ℝ) (hn : 1 ≤ n) (hp0 : (1 / 2 : ℝ) ≤ p) (hp1 : p ≤ 1) (hpp0 : (1 / 2 : ℝ) ≤ pp) (hpp1 : pp ≤ 1) :
    tY n p pp ≤ tN n p pp := by sorry

end SecretaryAdvice.BinaryLimit
