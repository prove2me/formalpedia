-- Prove2me | Theorems.Thm_WhitinPrice_LotSize_stationary_price_cubic
-- name    : WhitinPrice.LotSize.stationary_price_cubic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:48.55476+00:00
-- url     : https://prove2.me/theorems/1285dfcc-d6b5-4351-8e43-1abfe9adb1bb
-- title:
--   Section 2, Eqs. (6)–(7) — a stationary price satisfies Whitin’s cubic
-- statement:
--   Suppose $S,I,C>0$, annual demand at price $p$ is $D(p)=ap+b>0$, and the
--   derivative of the reduced annual profit
--   $P(p)=ap^2+bp-\sqrt{2SIC(ap+b)}-k(ap+b)-f$ vanishes at $p$.
--   Then $p$ satisfies Whitin's cubic:
--
--   $$
--   8a^3p^3+(16a^2b-8ka^3)p^2
--   +(10ab^2-12ka^2b+2k^2a^3)p
--   +2b^3-4kab^2+2k^2a^2b-SICa^2=0.
--   $$
--
--   This is a necessary algebraic condition for a profit-maximizing price; it does
--   not say that every root is optimal.
--
--   **Formalization Note** No sign is imposed on the demand slope $a$, the intercept
--   $b$, $k$, or $f$. The derivative is represented by `HasDerivAt` with value zero,
--   and positive demand keeps the square-root term differentiable.
-- source:
--   Whitin, Inventory Control and Price Theory, Management Sci. 2 (1955), p. 62, Section 2, Eqs. (6)–(7)

import Mathlib
import Definitions.Def_WhitinPrice_LotSize_Model

namespace WhitinPrice.LotSize

/-- Whitin (1955), §2, Eqs. (6)–(7): the displayed cubic is a necessary
condition for a stationary price. -/
theorem stationary_price_cubic (S I C k f a b p : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C)
    (hD : 0 < demand a b p)
    (hstat : HasDerivAt (reducedProfit S I C k f a b) 0 p) :
    8 * a ^ 3 * p ^ 3 + (16 * a ^ 2 * b - 8 * k * a ^ 3) * p ^ 2 +
      (10 * a * b ^ 2 - 12 * k * a ^ 2 * b + 2 * k ^ 2 * a ^ 3) * p +
      2 * b ^ 3 - 4 * k * a * b ^ 2 + 2 * k ^ 2 * a ^ 2 * b - S * I * C * a ^ 2 = 0 := by sorry

end WhitinPrice.LotSize
