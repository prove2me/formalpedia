-- Prove2me | Theorems.Thm_RevenueManagement_bernoulli_marginal_values
-- name    : RevenueManagement.bernoulli_marginal_values
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:48:26.517911+00:00
-- url     : https://prove2.me/theorems/82d9f4d8-2d3e-4a60-9578-f003aaa2bab3
-- title:
--   Proposition 5.2: under Assumption 7.2 the expected marginal value of capacity ΔVₜ(x) of the Bernoulli-demand program (5.12) is decreasing in t and in x
-- statement:
--   For the Bernoulli-demand model (5.12) with a revenue rate $r(t, d) = d\,p(t, d)$ concave in
--   $d$ on $[0, 1]$ (Assumption 7.2), for every period $1 \le t \le T$ and inventory
--   $x \ge 1$: (i) $\Delta V_{t+1}(x) \le \Delta V_t(x)$, the marginal value of capacity
--   decreases as time elapses, and (ii) $\Delta V_t(x + 1) \le \Delta V_t(x)$, it decreases in
--   the remaining capacity. With more time remaining the optimal price is higher, and with more
--   capacity it is lower.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 203, Proposition 5.2 (proof in Appendix 5.A, pp. 238-239)

import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

theorem bernoulli_marginal_values (p : ℕ → ℝ → ℝ) (T : ℕ)
    (hr : ∀ t, ConcaveOn ℝ (Set.Icc 0 1) (revenueRate p t)) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T)
    (hx : 1 ≤ x) :
    bernoulliDelta p T (t + 1) x ≤ bernoulliDelta p T t x ∧
      bernoulliDelta p T t (x + 1) ≤ bernoulliDelta p T t x := by sorry

end RevenueManagement
