-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_lemma_7
-- name    : WaitTimePricing.Existence.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:45.337017+00:00
-- url     : https://prove2.me/theorems/9004afec-d2ba-4b02-8bb8-eb1cbdd59ddb
-- title:
--   Lemma 7 — $\bar g=\lim_{j\to\infty}K^{\bar g}_{2^j}(0)$
-- statement:
--   The slope adjustments at $0$ of Algorithm 1 run with $g=\bar g$ converge to $\bar g$:
--   $$\bar g=\lim_{j\to\infty}K^{\bar g}_{2^j}(0).$$
--
--   This is the step from the shooting construction to the boundary condition (13).
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 38, Lemma 7 (Appendix B, proof of Proposition 7)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 38, Lemma 7 (Appendix B, proof of Proposition 7).

`ḡ = lim_{j→∞} K^ḡ_{2^j}(0)`. -/
theorem lemma_7 (M : Model) (hM : M.Standing) (obj : Objective) :
    Tendsto (fun j : ℕ => KgN M obj (gbar M obj) (2 ^ j) 0) atTop (nhds (gbar M obj)) := by sorry

end WaitTimePricing.Existence
