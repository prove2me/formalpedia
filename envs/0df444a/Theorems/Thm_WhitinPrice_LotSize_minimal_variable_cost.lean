-- Prove2me | Theorems.Thm_WhitinPrice_LotSize_minimal_variable_cost
-- name    : WhitinPrice.LotSize.minimal_variable_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:20.928105+00:00
-- url     : https://prove2.me/theorems/2aa31767-1efb-450e-8201-9432323b8ac7
-- title:
--   Section 2, Eq. (4) — variable cost at the economic lot size
-- statement:
--   Under positive annual demand $D$, setup cost $S$, carrying-rate factor $I$, and
--   unit purchase cost $C$, substitute the economic lot size
--   $Q^*=\sqrt{2DS/(IC)}$ into the total variable cost. For any operating cost $k$,
--
--   $$
--   \operatorname{TVC}(D,Q^*)=\sqrt{2DSIC}+kD.
--   $$
--
--   This identity supplies the inventory-cost term in the reduced annual profit.
--
--   **Formalization Note** The stated positivity hypotheses rule out total-division
--   and square-root values outside the economic domain.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 62, Section 2, Eq. (4)

import Mathlib
import Definitions.Def_WhitinPrice_LotSize_Model

namespace WhitinPrice.LotSize

/-- Whitin (1955), §2, Eq. (4). -/
theorem minimal_variable_cost (S I C k D : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C) (hD : 0 < D) :
    tvc S I C k D (Real.sqrt (2 * D * S / (I * C))) =
      Real.sqrt (2 * D * S * I * C) + k * D := by sorry

end WhitinPrice.LotSize
