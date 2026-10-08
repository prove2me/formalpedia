-- Prove2me | Theorems.Thm_WhitinPrice_LotSize_optimal_price_cubic
-- name    : WhitinPrice.LotSize.optimal_price_cubic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:35.553775+00:00
-- url     : https://prove2.me/theorems/a2a3c484-1ab3-4185-96b3-0b21eb6ae41d
-- title:
--   Section 2, Eqs. (3), (7) — joint profit maximizers use EOQ and satisfy Whitin’s cubic
-- statement:
--   Let $S,I,C>0$, and let $a,b,k,f$ be arbitrary real constants. At price $p$,
--   annual demand is $D(p)=ap+b$; for lot size $Q$, annual profit is
--   $\Pi(p,Q)=D(p)p-\operatorname{TVC}(D(p),Q)-f$. Suppose $D(p)>0$, $Q>0$, and
--   $(p,Q)$ maximizes $\Pi$ among all pairs $(p',Q')$ with $D(p')>0$ and $Q'>0$.
--   Then the lot size is the economic order quantity
--
--   $$
--   Q=\sqrt{\frac{2D(p)S}{IC}},
--   $$
--
--   and the price satisfies
--
--   $$
--   8a^3p^3+(16a^2b-8ka^3)p^2
--   +(10ab^2-12ka^2b+2k^2a^3)p
--   +2b^3-4kab^2+2k^2a^2b-SICa^2=0.
--   $$
--
--   This joins the inventory decision to the price decision. The cubic is only a
--   necessary condition: it may have roots that do not maximize profit.
--
--   **Formalization Note** The joint maximum is over positive demand and positive
--   lot size, with the unrestricted real price encoded in the feasible pair. The
--   positivity of $S,I,C$ is an explicit reading of the paper's costs; no sign of
--   $a,b,k,f$ is assumed.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), pp. 61–62, Section 2, Eqs. (3), (7)

import Mathlib
import Definitions.Def_WhitinPrice_LotSize_Model

namespace WhitinPrice.LotSize

/-- Whitin (1955), §2, Eqs. (3) and (7): a joint profit maximizer uses
the EOQ lot size and its price satisfies the necessary cubic equation. -/
theorem optimal_price_cubic (S I C k f a b p Q : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C)
    (hD : 0 < demand a b p) (hQ : 0 < Q)
    (hmax : IsMaxOn
      (fun z : ℝ × ℝ => profit S I C k f a b z.1 z.2)
      {z : ℝ × ℝ | 0 < demand a b z.1 ∧ 0 < z.2} (p, Q)) :
    Q = Real.sqrt (2 * demand a b p * S / (I * C)) ∧
      8 * a ^ 3 * p ^ 3 + (16 * a ^ 2 * b - 8 * k * a ^ 3) * p ^ 2 +
        (10 * a * b ^ 2 - 12 * k * a ^ 2 * b + 2 * k ^ 2 * a ^ 3) * p +
        2 * b ^ 3 - 4 * k * a * b ^ 2 + 2 * k ^ 2 * a ^ 2 * b - S * I * C * a ^ 2 = 0 := by sorry

end WhitinPrice.LotSize
