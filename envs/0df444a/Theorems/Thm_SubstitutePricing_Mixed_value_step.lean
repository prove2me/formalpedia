-- Prove2me | Theorems.Thm_SubstitutePricing_Mixed_value_step
-- name    : SubstitutePricing.Mixed.value_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:52.976296+00:00
-- url     : https://prove2.me/theorems/4dfcbebb-c17f-4959-88fe-3daa3acef686
-- title:
--   Proof of Proposition 2, p. 338 — π_t(x) − π_{t−1}(x) = λ(m_t(x) − μ)
-- statement:
--   In the mixed pricing model, let $t \ge 1$, let $x$ be an inventory vector, and let $m$ solve the margin equation (15) for period $t$ and inventory $x$. Then the mixed-pricing value function satisfies
--
--   $$
--   \pi_t(x) - \pi_{t-1}(x) = \lambda\,(m - \mu).
--   $$
--
--   Summed over periods with the boundary $\pi_0 = 0$, this gives the revenue formula $\pi_t(x) = \lambda \sum_{s=1}^t [m_s(x) - \mu]$ of Proposition 2.
--
--   **Formalization Note** $\pi_t$ is the supremum over nonnegative dynamic prices, as printed. The paper does not verify that the optimal prices $\Delta^i\pi_{t-1}(x) + m_t$ are nonnegative; the statement is posed as printed (see the mission description).
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 338, App. A, proof of Proposition 2

import Definitions.Def_SubstitutePricing_Mixed_Model

namespace SubstitutePricing.Mixed
/-- The one-period recursion of the proof of Proposition 2: `πₜ(x) − πₜ₋₁(x) = λ(mₜ − μ)`. -/
theorem value_step (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) (m : ℝ) (hm : M.lhs15 t x m = M.rhs15 t x) :
    M.piM t x - M.piM (t - 1) x = M.lam * (m - M.μ) := by sorry
end SubstitutePricing.Mixed
