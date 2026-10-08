-- Prove2me | Theorems.Thm_RevShareCoord_Competing_cournot_wI_monotone
-- name    : RevShareCoord.Competing.cournot_wI_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T00:53:26.551175+00:00
-- url     : https://prove2.me/theorems/a0058655-8d41-42a5-8e68-9741d3e6ce81
-- title:
--   Sec. 4.1.2 — the Cournot coordinating price w^I is increasing in β and in n
-- statement:
--   Let $0 < c < 1$ and
--   $$w^I(\beta, n) = c + \frac{\beta(n-1)(1-c)}{2+2\beta(n-1)}$$
--   be the coordinating wholesale price of the Cournot example with $n$ retailers and substitution parameter $\beta$. Then:
--
--   1. for every $n \ge 2$, $w^I$ is strictly increasing in $\beta \in [0,1)$;
--   2. for every $\beta \in (0,1)$, $w^I$ is strictly increasing in the number of retailers $n \ge 1$.
--
--   As competition increases by either measure, a higher wholesale price is needed to moderate it.
--
--   **Formalization Note** The page says "increasing". At $n = 1$ the price does not depend on $\beta$, and at $\beta = 0$ it does not depend on $n$, so strict monotonicity is stated exactly where it holds.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 19 (PDF p. 20), Section 4.1.2, sentence after the display of w^I

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

/-- **Sec. 4.1.2, `w^I` increases with competition (p. 19).** Let `0 < c < 1` and
`w^I(β, n) = c + β(n − 1)(1 − c)/(2 + 2β(n − 1))`.
1. For every `n ≥ 2`, `w^I` is strictly increasing in `β ∈ [0, 1)`.
2. For every `β ∈ (0, 1)`, `w^I` is strictly increasing in the number of retailers `n ≥ 1`. -/
theorem cournot_wI_monotone (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    (∀ n : ℕ, 2 ≤ n → StrictMonoOn (fun β => cournotWI β n c) (Set.Ico 0 1)) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ m k : ℕ, 1 ≤ m → m < k →
        cournotWI β m c < cournotWI β k c := by sorry

end RevShareCoord.Competing
