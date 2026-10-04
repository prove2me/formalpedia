-- Prove2me | Theorems.Thm_SeatInventory_Distinct_emsr_antitone
-- name    : SeatInventory.Distinct.emsr_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:05:35.391238+00:00
-- url     : https://prove2.me/theorems/3d2d48e3-fc96-431e-8f1c-2119f7389ea0
-- title:
--   Eqs. (6.1)-(6.2) — EMSR(S) is non-increasing in S
-- statement:
--   Let a fare class have average fare $f \ge 0$ and integer-valued requests $r$. Then the tail probability $\bar P(S) = P[r \ge S]$ is a non-increasing function of $S$, and so is the expected marginal seat revenue
--   $$
--   \mathrm{EMSR}(S) = \bar P(S)\cdot f .
--   $$
--
--   Monotonicity of the marginal values is what makes allocating seats one at a time, always to the largest remaining marginal value, revenue-maximising.
--
--   **Formalization Note** The thesis says "decreasing"; its justification (point probabilities are nonnegative) gives only non-increasing, and strict decrease is false when $r$ is bounded, so the statement is `Antitone`. Nonnegativity of the fare is required for the EMSR part and is a standing convention of the model (a fare is a price received).
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 142, Eqs. (6.1)-(6.2) and the paragraph after them

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel

namespace SeatInventory.Distinct

/-- Belobaba 1987, Eqs. (6.1)–(6.2), p. 142: `P̄(S) = P[r ≥ S]` is non-increasing in `S`, hence so
is `EMSR(S) = P̄(S) · f` for a nonnegative fare `f`. -/
theorem emsr_antitone (f : ℝ) (hf : 0 ≤ f) (p : PMF ℕ) :
    Antitone (tailProb p) ∧ Antitone (emsr f p) := by sorry

end SeatInventory.Distinct
