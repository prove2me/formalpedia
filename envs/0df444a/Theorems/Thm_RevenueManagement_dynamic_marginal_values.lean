-- Prove2me | Theorems.Thm_RevenueManagement_dynamic_marginal_values
-- name    : RevenueManagement.dynamic_marginal_values
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:31:19.595698+00:00
-- url     : https://prove2.me/theorems/425a6dcc-f369-4264-aee3-6f32276f5a43
-- title:
--   Proposition 2.2: the increments ΔVₜ(x) of the dynamic model are decreasing in the remaining capacity x and decreasing in time t
-- statement:
--   For the dynamic model (2.17) with an arrival model $\lambda_j(t)$ and nonnegative prices,
--   for every period $1 \le t \le T$ and $x \ge 1$: (i) $\Delta V_t(x+1) \le \Delta V_t(x)$,
--   the value of additional capacity has decreasing marginal benefit; (ii)
--   $\Delta V_{t+1}(x) \le \Delta V_t(x)$, the marginal value at a given remaining capacity
--   decreases with time.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 60, Proposition 2.2 (proof in Appendix 2.A, pp. 78-79)

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem dynamic_marginal_values (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T : ℕ)
    (hlam : IsArrivalModel lam n) (hp : ∀ j, 0 ≤ p j) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T)
    (hx : 1 ≤ x) :
    dynDelta lam p n T t (x + 1) ≤ dynDelta lam p n T t x ∧
      dynDelta lam p n T (t + 1) x ≤ dynDelta lam p n T t x := by sorry

end RevenueManagement
