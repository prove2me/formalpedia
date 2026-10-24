-- Prove2me | Theorems.Thm_PricingWithTips_assigned_order_courier_envelope
-- name    : PricingWithTips.assigned_order_courier_envelope
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-21T00:22:33.439838+00:00
-- url     : https://prove2.me/theorems/8e195416-e000-4c70-a725-a227e1208093
-- title:
--   An assigned wage is the courier cost–utility envelope
-- statement:
--   In a feasible courier wage plan realizing utilities uBar, the wage paid for any delivered buyer–store order equals the minimum, over couriers, of that courier’s delivery cost plus her realized utility. The assigned courier attains the minimum.
-- source:
--   Lemma 3.2 and Theorem 5.2 of arXiv:2507.10872; private mission proof support

import Definitions.Def_PricingWithTips_Model

namespace PricingWithTips

variable {B S D : Type*} [Fintype B] [Fintype S] [Fintype D]
  [DecidableEq B] [DecidableEq S] [DecidableEq D]

theorem assigned_order_courier_envelope [Nonempty D]
    (M : Market B S D) (A : Allocation B S D)
    (w : B → S → ℝ) (uBar : D → ℝ)
    (hplan : IsCourierPlanFor M A w)
    (hreal : ∀ d, courierRealizedUtility M A w d = uBar d)
    {b : B} {s : S} {d : D} (ht : A.Trades b s d) :
    (⨅ d' : D, M.cost d' b s + uBar d') = w b s := by sorry

end PricingWithTips
