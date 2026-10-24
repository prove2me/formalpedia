-- Prove2me | Theorems.Thm_PricingWithTips_corollary_4_5_minimum_cost_courier_assignment
-- name    : PricingWithTips.corollary_4_5_minimum_cost_courier_assignment
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:21:44.436986+00:00
-- url     : https://prove2.me/theorems/e6d83d36-6d3e-4557-892f-3a50c12c3df0
-- title:
--   Corrected Corollary 4.5 — full utilization with a minimum-cost courier assignment
-- statement:
--   Let a finite delivery market have buyers, stores, and at least one courier. Fix a feasible allocation A in which every courier delivers. Assume A minimizes total delivery cost among all feasible courier assignments of exactly the same buyer–store orders (equivalently, A maximizes welfare among allocations with that buyer–store matching). Then there are store prices, courier payments, and tips that support A as a with-tip equilibrium.
--
--   $$
--   \bigl[\text{all couriers work in }A\bigr]\ \land\
--   \bigl[\forall A'\text{ with the same buyer–store orders},\ W(A')\le W(A)\bigr]
--   \ \Longrightarrow\
--   \exists p,w,t,\ \operatorname{WithTipEquilibrium}(M,A,p,w,t).
--   $$
--
--   The cost-minimality condition is necessary to exclude crossed courier assignments whose couriers would each prefer the other's order. A welfare-optimal allocation automatically satisfies it, so this corrected corollary retains the role of the full-utilization case in Theorem 5.2.
--
--   **Formalization Note** The buyer–store orders are compared through the store projection of each buyer's optional assignment. The theorem preserves the given courier assignment; it does not silently rematch couriers.
-- source:
--   https://arxiv.org/abs/2507.10872, Section 4, Corollary 4.5 (p. 18), proof in Appendix C (p. 33); corrected to require minimum-cost courier assignment after the accepted disproof of the original fixed-allocation statement.

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem corollary_4_5_minimum_cost_courier_assignment [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (hfull : ∀ d, A.CourierWorks d)
    (hminimum : ∀ A' : Allocation B S D,
      (∀ b, (A'.assigned b).map Prod.fst = (A.assigned b).map Prod.fst) →
        welfare M A' ≤ welfare M A) :
    HasWithTipEquilibriumAt M A := by sorry

end PricingWithTips
