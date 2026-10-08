-- Prove2me | Theorems.Thm_WhitinPrice_LotSize_optimal_lot_size
-- name    : WhitinPrice.LotSize.optimal_lot_size
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:21.285171+00:00
-- url     : https://prove2.me/theorems/36a6f344-b0c2-4a21-879d-cd5d75ced275
-- title:
--   Section 2, Eq. (3) — the economic lot size uniquely minimizes variable cost
-- statement:
--   Let annual demand $D$ and the setup cost $S$, carrying-rate factor $I$, and unit
--   purchase cost $C$ all be positive. Let $k$ be any per-unit operating cost. Among
--   positive lot sizes, the unique minimizer of the annual variable cost is
--
--   $$
--   Q^*=\sqrt{\frac{2DS}{IC}},\qquad
--   \operatorname{TVC}(D,Q^*)\leq\operatorname{TVC}(D,Q)
--   \quad(Q>0),
--   $$
--
--   with equality only when $Q=Q^*$. This is the lot-size choice used when annual
--   profit is optimized jointly over price and order quantity.
--
--   **Formalization Note** Positivity of $S,I,C,D$ and $Q$ makes the square root and
--   division represent the paper's cost model. The uniqueness and global comparison
--   make the paper's phrase “optimal value of $Q$” explicit.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 62, Section 2, Eqs. (2)–(3)

import Mathlib
import Definitions.Def_WhitinPrice_LotSize_Model

namespace WhitinPrice.LotSize

/-- Whitin (1955), §2, Eq. (3), with global optimality and its equality case explicit. -/
theorem optimal_lot_size (S I C k D : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C) (hD : 0 < D) :
    0 < Real.sqrt (2 * D * S / (I * C)) ∧
      ∀ Q : ℝ, 0 < Q →
        tvc S I C k D (Real.sqrt (2 * D * S / (I * C))) ≤ tvc S I C k D Q ∧
          (tvc S I C k D (Real.sqrt (2 * D * S / (I * C))) = tvc S I C k D Q →
            Q = Real.sqrt (2 * D * S / (I * C))) := by sorry

end WhitinPrice.LotSize
