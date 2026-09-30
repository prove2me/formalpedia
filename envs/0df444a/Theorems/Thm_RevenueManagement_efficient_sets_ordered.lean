-- Prove2me | Theorems.Thm_RevenueManagement_efficient_sets_ordered
-- name    : RevenueManagement.efficient_sets_ordered
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:33:26.202423+00:00
-- url     : https://prove2.me/theorems/938714b7-4c3c-4f4c-b68f-b975ac48ac0b
-- title:
--   Efficient sets are ordered (Sect. 2.6.2.3): if S' is efficient and Q(S) ≤ Q(S'), then R(S) ≤ R(S')
-- statement:
--   The efficient sets can be indexed so that both the purchase probabilities and the expected
--   revenues increase with the index: for any set $S$ and any efficient set $S'$,
--   $Q(S) \le Q(S')$ implies $R(S) \le R(S')$. This is the book's ordering statement in the
--   form that holds with ties; the strict form fails when two efficient sets have equal revenue,
--   since Definition 2.1 does not make a set with the same revenue and larger purchase
--   probability inefficient.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 68, Sect. 2.6.2.3 ('if the collection of m efficient sets is indexed such that Q(S1) < Q(S2) < ··· < Q(Sm), then R(S1) < R(S2) < ··· < R(Sm) as well')

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem efficient_sets_ordered {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (p : Fin n → ℝ)
    (S S' : Finset (Fin n)) (hS' : IsEfficient P p S')
    (hQ : purchaseProb P S ≤ purchaseProb P S') :
    expRevenue P p S ≤ expRevenue P p S' := by sorry

end RevenueManagement
