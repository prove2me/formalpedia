-- Prove2me | Theorems.Thm_SuttonBartoRL_ImportanceSampling_return_eq_flat_partial_returns
-- name    : SuttonBartoRL.ImportanceSampling.return_eq_flat_partial_returns
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:30:56.380983+00:00
-- url     : https://prove2.me/theorems/eccb2431-1717-48d8-bcc0-74735c282d4a
-- title:
--   The return as a sum of flat partial returns
-- statement:
--   For any rewards $R_1, R_2, \dots$, any discount rate $\gamma$ and times $0 \le t < T$,
--
--   $$
--   G_t = R_{t+1} + \gamma R_{t+2} + \dots + \gamma^{T-t-1} R_T = (1 - \gamma) \sum_{h=t+1}^{T-1} \gamma^{h-t-1} \bar G_{t:h} + \gamma^{T-t-1} \bar G_{t:T},
--   $$
--
--   where $\bar G_{t:h} = R_{t+1} + \dots + R_h$ is the flat partial return. Read with $\gamma \in [0,1)$, the return is an average of flat partial returns in which horizon $h$ receives the weight $(1-\gamma)\gamma^{h-t-1}$ of "terminating" at $h$. This decomposition underlies the discounting-aware importance-sampling estimators (5.9)–(5.10).
--
--   **Formalization Note** The book introduces the decomposition "for any $\gamma \in [0,1)$"; the identity is algebraic and is stated here for every real $\gamma$, which is more general than the book's reading.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, §5.8, display decomposing G_t into flat partial returns, p. 113

import Mathlib
import Definitions.Def_SuttonBartoRL_ImportanceSampling_Returns

namespace SuttonBartoRL.ImportanceSampling

/-- Sutton & Barto (2018), §5.8, p. 113: the return is a sum of flat partial returns,
`G_t = (1 - γ) Σ_{h=t+1}^{T-1} γ^{h-t-1} Ḡ_{t:h} + γ^{T-t-1} Ḡ_{t:T}` for `0 ≤ t < T`. -/
theorem return_eq_flat_partial_returns (R : ℕ → ℝ) (γ : ℝ) (t T : ℕ) (htT : t < T) :
    discountedReturn R γ t T =
      (1 - γ) * ∑ h ∈ Finset.Ioo t T, γ ^ (h - t - 1) * flatPartialReturn R t h +
        γ ^ (T - t - 1) * flatPartialReturn R t T := by sorry

end SuttonBartoRL.ImportanceSampling
