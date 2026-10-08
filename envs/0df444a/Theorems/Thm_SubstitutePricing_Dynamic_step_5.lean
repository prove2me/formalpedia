-- Prove2me | Theorems.Thm_SubstitutePricing_Dynamic_step_5
-- name    : SubstitutePricing.Dynamic.step_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:19.052956+00:00
-- url     : https://prove2.me/theorems/7b5d3a47-3448-4d0d-905c-df6f1827d89a
-- title:
--   Step 5 — feasible optimal prices and Bellman recursion
-- statement:
--   For an inventory with at least one stocked variate and $t\geq1$, let $m$ solve the period-$t$ margin equation. The candidate price $r_i^*=\Delta^i\pi_{t-1}(x)+m$ is positive for each $i\in S(x)$, the full price vector is feasible, and it attains the Bellman objective over all nonnegative price vectors. Moreover,
--
--   $$
--   \pi_t(x)=\operatorname{obj}_{\pi_{t-1}}(x,r^*)=\lambda(m-\mu)+\pi_{t-1}(x).
--   $$
--
--   This one-period value identity is the last step before the paper sums revenues across remaining periods.
--
--   **Formalization Note** Off-stock prices are set to zero and have no effect. Explicit attainment rules out relying on a default value of the real supremum.
-- source:
--   Dong, Kouvelis, Tian, Dynamic Pricing and Inventory Control of Substitute Products, Manufacturing & Service Operations Management 11(2) (2009), p. 336, Appendix A, proof of Theorem 1, Step 5, (22)

import Definitions.Def_SubstitutePricing_Dynamic_Model

namespace SubstitutePricing.Dynamic
/-- Step 5: the candidate prices are feasible and attain the Bellman value (22). -/
theorem step_5 (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) (hS : (M.S x).Nonempty) (m : ℝ)
    (hm : M.marginLHS m = M.sigma t x) :
    (∀ i ∈ M.S x, 0 < M.rstar t x m i) ∧
    M.rstar t x m ∈ M.feasible ∧
    IsMaxOn (M.obj (M.pi (t - 1)) x) M.feasible (M.rstar t x m) ∧
    M.pi t x = M.obj (M.pi (t - 1)) x (M.rstar t x m) ∧
    M.pi t x = M.lam * (m - M.μ) + M.pi (t - 1) x := by sorry
end SubstitutePricing.Dynamic
