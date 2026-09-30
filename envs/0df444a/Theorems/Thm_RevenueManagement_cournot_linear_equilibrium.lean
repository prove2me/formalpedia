-- Prove2me | Theorems.Thm_RevenueManagement_cournot_linear_equilibrium
-- name    : RevenueManagement.cournot_linear_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T01:05:06.864466+00:00
-- url     : https://prove2.me/theorems/324d9494-78a3-451f-811c-5d3a65ad6e83
-- title:
--   Example 8.15, Eq. (8.19)-(8.20): with linear demand p = a − X and marginal cost c, the symmetric quantities x* = (a − c)/(n + 1) form a Cournot equilibrium with price p* = c + (a − c)/(n + 1)
-- statement:
--   In the $n$-firm Cournot game with inverse demand $p(X) = a - X$, $a > c$, and constant
--   marginal cost $c$, the symmetric profile $x_i^* = (a - c)/(n + 1)$ is a Nash equilibrium:
--   no firm gains by any nonnegative deviation. The market-clearing price is
--   $p^* = a - n x^* = c + (a - c)/(n + 1)$, strictly above marginal cost.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 377-378, Example 8.15, Eq. (8.17)-(8.20)

import Definitions.Def_RevenueManagement_competition

namespace RevenueManagement

theorem cournot_linear_equilibrium {n : ℕ} (a c : ℝ) (hac : c < a) :
    (∀ (i : Fin n) (xi : ℝ), 0 ≤ xi →
      cournotPayoff a c (Function.update (fun _ => (a - c) / (n + 1)) i xi) i ≤
        cournotPayoff a c (fun _ => (a - c) / (n + 1)) i) ∧
    a - n * ((a - c) / (n + 1)) = c + (a - c) / (n + 1) := by sorry

end RevenueManagement
