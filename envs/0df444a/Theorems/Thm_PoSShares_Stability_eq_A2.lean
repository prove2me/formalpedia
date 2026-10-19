-- Prove2me | Theorems.Thm_PoSShares_Stability_eq_A2
-- name    : PoSShares.Stability.eq_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:42.387046+00:00
-- url     : https://prove2.me/theorems/d3b3f4f8-f0d8-4f73-9a50-22517f887d51
-- title:
--   (A2) — the share increment $\pi_{t+1} - \pi_t = R_{t+1}(\mathbf{1}_{S_{t+1}} - \pi_t)/N_{t+1}$
-- statement:
--   In the PoS model, for every date $t \ge 0$ and every outcome, the buy-and-hold investor's share satisfies
--   $$\pi_{t+1} - \pi_t = R_{t+1}\,\frac{\mathbf{1}_{S_{t+1}} - \pi_t}{N_{t+1}},$$
--   where $N_{t+1} = N_t + R_{t+1}$ is the coin supply and $\mathbf{1}_{S_{t+1}}$ indicates that the investor is selected at $t+1$.
--
--   This is the basic increment identity behind the martingale property and the variance computations.
--
--   **Formalization Note.** The identity is deterministic: it uses only $N_0 > 0$ and $R \ge 0$, not the selection rule.
-- source:
--   Roşu, Saleh, Evolution of Shares in a Proof-of-Stake Cryptocurrency, author's manuscript of July 30, 2020 (sha256 90d9c06b…2b35eb), p. 17, proof of Proposition 1, (A2)

import Mathlib
import Definitions.Def_PoSShares_Stability_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PoSShares.Stability

/-- **(A2)**, proof of Proposition 1, p. 17. Roşu, Saleh, *Evolution of Shares in a Proof-of-Stake Cryptocurrency*, author's manuscript of
July 30, 2020 (sha256 90d9c06b…2b35eb).

The total number of coins satisfies `N_{t+1} = N_t + R_{t+1}`, therefore the share of the
buy-and-hold investor satisfies
`π_{t+1} − π_t = R_{t+1} (1_{S_{t+1}} − π_t) / N_{t+1}` for every date and every outcome.

**Formalization Note.** Stated for the step `t → t + 1` (`t ∈ ℕ`), i.e. the paper's `t ∈ ℕ₊`
shifted by one. Deterministic: only the structure's invariants (`N_0 > 0`, `R ≥ 0`) are used,
not the selection rule. -/
theorem eq_A2 {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (t : ℕ) (ω : Ω) :
    share M (t + 1) ω - share M t ω =
      M.R (t + 1) * (M.ξ (t + 1) ω - share M t ω) / coinSupply M.N₀ M.R (t + 1) := by sorry

end PoSShares.Stability
