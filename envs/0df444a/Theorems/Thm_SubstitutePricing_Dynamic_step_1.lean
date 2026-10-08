-- Prove2me | Theorems.Thm_SubstitutePricing_Dynamic_step_1
-- name    : SubstitutePricing.Dynamic.step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:04.537127+00:00
-- url     : https://prove2.me/theorems/a1cb0ccd-d7a0-4773-a402-f982edb3079c
-- title:
--   Step 1 — nonnegative marginal inventory value
-- statement:
--   Under the model assumptions, one more unit of any currently stocked variate has nonnegative marginal value at every remaining horizon $t$:
--
--   $$
--   \Delta^i\pi_t(x)=\pi_t(x)-\pi_t(x-e^i)\geq0 \qquad(i\in S(x)).
--   $$
--
--   This is the inventory monotonicity fact used in Step 1 and later to establish that the candidate optimal prices meet the paper's nonnegative price restriction.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 334, Appendix A, proof of Theorem 1, Step 1

import Definitions.Def_SubstitutePricing_Dynamic_Model

namespace SubstitutePricing.Dynamic
/-- The marginal inventory value used in Step 1 is nonnegative. -/
theorem step_1 (M : Model) (hM : M.Assumptions)
    (t : ℕ) (x : Fin M.n → ℕ) (i : Fin M.n) (hi : i ∈ M.S x) :
    0 ≤ M.delta t i x := by sorry
end SubstitutePricing.Dynamic
