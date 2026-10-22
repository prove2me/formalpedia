-- Prove2me | Theorems.Thm_PersonalizedAssortment_IB_revenue_eq_expected_sales
-- name    : PersonalizedAssortment.IB.revenue_eq_expected_sales
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T01:58:08.942831+00:00
-- url     : https://prove2.me/theorems/6c8e9a75-7de9-42f1-9493-259f64b3b7ee
-- title:
--   Expected revenue equals $\mathbb E[\sum_i r_i(c_i-I_i^T)]$
-- statement:
--   Let $S^t(\cdot)$ be any selection rule and let $I^0=c,I^1,\dots,I^T$ be the inventory process it generates. The expected revenue collected over the horizon is
--   $$\mathrm{Rev}=\sum_{t=1}^T\mathbb E\Big[\sum_{i=1}^n r_i\,\varphi_i^{z_t}\big(S^t(I^{t-1})\big)\,\mathbb 1[I_i^{t-1}>0]\Big].$$
--   It equals the revenue of the units sold by the end of the horizon:
--   $$\mathrm{Rev}\;=\;\mathbb E\Big[\sum_{i=1}^n r_i\,(c_i-I_i^T)\Big].$$
--
--   This is the identity the proof of Theorem 1 uses for the numerator of the competitive ratio.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1549, Section A.3, proof of Theorem 1 ('On the other hand, the expected revenue of the inventory-balancing algorithm is equal to ...')

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel
import Definitions.Def_PersonalizedAssortment_IB_InventoryBalancing

namespace PersonalizedAssortment.IB

/-- §A.3, p. 1549: the expected revenue of the algorithm equals `𝔼[∑_{i=1}^n r_i (c_i - I_i^T)]`,
the revenue of the units sold by the end of the horizon. -/
theorem revenue_eq_expected_sales {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (c : Fin n → ℕ)
    (φ : Z → ChoiceModel n) {T : ℕ} (z : Fin T → Z)
    (sel : Fin T → (Fin n → ℕ) → Finset (Fin n)) :
    ibRevenue r c φ z sel =
      expectInv φ z sel c T le_rfl (fun I => ∑ i : Fin n, r i * ((c i : ℝ) - (I i : ℝ))) := by sorry

end PersonalizedAssortment.IB
