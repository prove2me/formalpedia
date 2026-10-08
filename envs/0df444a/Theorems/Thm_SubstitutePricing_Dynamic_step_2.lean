-- Prove2me | Theorems.Thm_SubstitutePricing_Dynamic_step_2
-- name    : SubstitutePricing.Dynamic.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:59.551074+00:00
-- url     : https://prove2.me/theorems/449bc31d-6563-44d3-816d-250b591a5577
-- title:
--   Step 2 — prices and interior choice probabilities
-- statement:
--   Fix an inventory $x$ with at least one stocked variate. Every finite real price vector produces positive purchase probabilities on $S(x)$ and a positive outside-option probability; each is below one and their sum is one. The inverse relation is
--
--   $$
--   r_i=a_i-u_0-\mu\log P_i(x,r)+\mu\log P_0(x,r)\qquad(i\in S(x)).
--   $$
--
--   Conversely, every positive probability vector on the stocked variates and the outside option whose coordinates sum to one is obtained from these inverse prices. This is the correspondence used to optimize marginal revenue in probability coordinates.
--
--   **Formalization Note** The nonempty-stock hypothesis is needed for the strict inequality $P_0<1$. Coordinates outside $S(x)$ do not affect demand.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 335, Appendix A, proof of Theorem 1, Step 2, (16)–(18); p. 323, (7)

import Definitions.Def_SubstitutePricing_Dynamic_Model

namespace SubstitutePricing.Dynamic
/-- Step 2: finite prices correspond to interior choice probabilities, with inverse (18). -/
theorem step_2 (M : Model) (hM : M.Assumptions)
    (x : Fin M.n → ℕ) (hS : (M.S x).Nonempty) :
    (∀ r : Fin M.n → ℝ,
      (∀ i ∈ M.S x, 0 < M.P x r i ∧ M.P x r i < 1) ∧
      0 < M.P0 x r ∧ M.P0 x r < 1 ∧
      (∑ i ∈ M.S x, M.P x r i) + M.P0 x r = 1 ∧
      (∀ i ∈ M.S x,
        r i = M.a i - M.u0 - M.μ * Real.log (M.P x r i) +
          M.μ * Real.log (M.P0 x r))) ∧
    (∀ (p : Fin M.n → ℝ) (p0 : ℝ),
      (∀ i ∈ M.S x, 0 < p i) → 0 < p0 →
      (∑ i ∈ M.S x, p i) + p0 = 1 →
      let r : Fin M.n → ℝ :=
        fun i => M.a i - M.u0 - M.μ * Real.log (p i) + M.μ * Real.log p0
      (∀ i ∈ M.S x, M.P x r i = p i) ∧ M.P0 x r = p0) := by sorry
end SubstitutePricing.Dynamic
