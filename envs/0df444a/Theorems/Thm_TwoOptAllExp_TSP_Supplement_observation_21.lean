-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_observation_21
-- name    : TwoOptAllExp.TSP.Supplement.observation_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:49:24.079194+00:00
-- url     : https://prove2.me/theorems/4fbb4f8f-ba9b-4e31-96c0-45fa2b4595c9
-- title:
--   Observation 21 — $T_n=(39\cdot3^n-35)/2$
-- statement:
--   For every $n\ge0$, the common length $T_n=|\Omega_n|=|\bar\Omega_n|$ of the two canonical flip strings of Section 5 is
--
--   $$T_n=\frac{39\cdot3^n-35}{2}.$$
--
--   This gives the exponential run length in Corollary 26 and Theorem 3.
--
--   Differences from the source:
--   - encoding: T_n is introduced as |Ω_n| = |Ω̄_n| immediately before Observation 21 → (OmegaBar n).length = T n, where T n is defined as (Omega n).length; reason: retains the common-length equality from the source preamble as an explicit conclusion
--   - encoding: T_n = (39·3^n − 35)/2 → the equality cast to ℚ; reason: exact division, no natural-number truncation
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Observation 21, p. 31

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232

namespace TwoOptAllExp.TSP.Supplement

open MCA232 MCA232.Vx

/-- **Observation 21** (p. 31). For `n ≥ 0`, the common length
`T_n = |Ω_n| = |Ω̄_n|` equals `(39 · 3^n - 35) / 2`. -/
theorem observation_21 (n : ℕ) :
    (OmegaBar n).length = T n ∧ (T n : ℚ) = (39 * 3 ^ n - 35) / 2 := by sorry

end TwoOptAllExp.TSP.Supplement
