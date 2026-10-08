-- Prove2me | Theorems.Thm_SubstitutePricing_Dynamic_step_4_root
-- name    : SubstitutePricing.Dynamic.step_4_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:22.415021+00:00
-- url     : https://prove2.me/theorems/dc65d0ec-3e41-4cc0-bd0b-a3c3abcf30f4
-- title:
--   Step 4 — unique margin root of (21)
-- statement:
--   For real outside-option utility $u_0$, positive logit scale $\mu$, and positive right-hand side $\sigma$, equation (21) has exactly one real solution $m$, and that solution lies above $\mu$:
--
--   $$
--   \left(\frac{m}{\mu}-1\right)\exp\left(\frac{m+u_0}{\mu}\right)=\sigma,\qquad m>\mu.
--   $$
--
--   This supplies the unique margin used to construct the optimal choice probabilities and prices. The result is independent of a particular inventory or horizon.
--
--   **Formalization Note** Positivity of $\sigma$ corresponds to the paper's nonempty in-stock set.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), pp. 335–336, Appendix A, proof of Theorem 1, Step 4, (21)

import Definitions.Def_SubstitutePricing_Dynamic_Model

namespace SubstitutePricing.Dynamic
/-- Step 4: equation (21) has exactly one real solution, above the MNL scale. -/
theorem step_4_root (μ u0 σ : ℝ) (hμ : 0 < μ) (hσ : 0 < σ) :
    (∃! m : ℝ, (m / μ - 1) * Real.exp ((m + u0) / μ) = σ) ∧
    (∀ m : ℝ, (m / μ - 1) * Real.exp ((m + u0) / μ) = σ → μ < m) := by sorry
end SubstitutePricing.Dynamic
