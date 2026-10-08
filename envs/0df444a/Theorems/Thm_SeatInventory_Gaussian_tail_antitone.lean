-- Prove2me | Theorems.Thm_SeatInventory_Gaussian_tail_antitone
-- name    : SeatInventory.Gaussian.tail_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:00:36.852657+00:00
-- url     : https://prove2.me/theorems/010bc4d4-b6e0-4dad-a753-c81a0d1006ed
-- title:
--   Eq. (6.1)–(6.2) — the tail probability and EMSR are non-increasing in S
-- statement:
--   Let $\mu$ be any probability law of the number of requests $r$ on $\mathbb R$, and $f \ge 0$ a fare. Then the tail probability $\bar P(S) = P[r \ge S]$ and the expected marginal seat revenue $\mathrm{EMSR}(S) = \bar P(S)\cdot f$ are non-increasing functions of $S$:
--   $$S \le S' \implies \bar P(S') \le \bar P(S) \ \text{ and } \ \mathrm{EMSR}(S') \le \mathrm{EMSR}(S).$$
--
--   This is the monotonicity the EMSR framework relies on for any demand density: the comparison of the decreasing expected marginal revenue with the fixed lower fare is what yields a protection level.
--
--   **Formalization Note** The book states the claim for a probability density; the Lean statement holds for every probability measure on $\mathbb R$, which contains that case.
-- source:
--   Belobaba, Air Travel Demand and Airline Seat Inventory Management, MIT Flight Transportation Laboratory Report R87-7 (PhD thesis), 1987, p. 142, Eq. (6.1)-(6.2) and the sentence following them

import Mathlib
import Definitions.Def_SeatInventory_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace SeatInventory.Gaussian

/-- Belobaba (1987), Eq. (6.1)–(6.2), p. 142: for any law of the requests, `P̄(S) = P[r ≥ S]`
is non-increasing in `S`, and so is `EMSR(S) = P̄(S) · f` for a non-negative fare `f`. -/
theorem tail_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ) (hf : 0 ≤ f) :
    Antitone (tailProb μ) ∧ Antitone (emsr μ f) := by sorry

end SeatInventory.Gaussian
