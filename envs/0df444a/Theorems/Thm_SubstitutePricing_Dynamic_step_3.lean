-- Prove2me | Theorems.Thm_SubstitutePricing_Dynamic_step_3
-- name    : SubstitutePricing.Dynamic.step_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:17.669991+00:00
-- url     : https://prove2.me/theorems/fe36d38c-1108-41f5-86a6-7f76dd580dc9
-- title:
--   Step 3 — concavity in choice probabilities
-- statement:
--   Let $S$ be a finite set of variates and $\delta_i$ fixed marginal inventory values. On the domain where every $p_i$ for $i\in S$ and $p_0$ lies strictly between zero and one, the probability-parametrized marginal revenue
--
--   $$
--   \xi(p,p_0)=\lambda\sum_{i\in S}p_i\bigl[a_i-u_0-\mu\log p_i+\mu\log p_0-\delta_i\bigr]
--   $$
--
--   is concave. This is the curvature property used in the paper's probability-space optimization.
--
--   **Formalization Note** The assertion is concavity, as stated in Step 3. The printed claim of strict concavity on the full positive domain does not hold along scaling rays.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 335, Appendix A, proof of Theorem 1, Step 3; p. 323, (8)

import Definitions.Def_SubstitutePricing_Dynamic_Model

namespace SubstitutePricing.Dynamic
/-- Step 3: the probability-parametrized marginal revenue (8) is concave. -/
theorem step_3 (M : Model) (hM : M.Assumptions)
    (S : Finset (Fin M.n)) (δ : Fin M.n → ℝ) :
    ConcaveOn ℝ (M.positiveProbDomain S) (M.probObjective S δ) := by sorry
end SubstitutePricing.Dynamic
