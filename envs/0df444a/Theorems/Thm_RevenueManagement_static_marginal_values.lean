-- Prove2me | Theorems.Thm_RevenueManagement_static_marginal_values
-- name    : RevenueManagement.static_marginal_values
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:29:34.578122+00:00
-- url     : https://prove2.me/theorems/17315d09-4f27-4318-bbd3-35a0b777d406
-- title:
--   Proposition 2.1: the marginal values ΔVⱼ(x) of the static model are decreasing in the remaining capacity x and increasing in the number of stages j remaining
-- statement:
--   For the static model (2.3) with nonnegative prices and pmf demands, for every stage $j$ and
--   every $x \ge 1$: (i) $\Delta V_j(x+1) \le \Delta V_j(x)$, the marginal value is decreasing
--   in the remaining capacity ($V_j$ is concave on $\mathbb N$); (ii)
--   $\Delta V_{j+1}(x) \ge \Delta V_j(x)$, at a given capacity the marginal value increases in
--   the number of stages remaining.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 38, Proposition 2.1 (proof in Appendix 2.A, pp. 77-78, via Lemma 2-2.A.1)

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem static_marginal_values (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j))
    (hp : ∀ j, 0 ≤ p j) (j x : ℕ) (hx : 1 ≤ x) :
    staticDelta p f j (x + 1) ≤ staticDelta p f j x ∧
      staticDelta p f j x ≤ staticDelta p f (j + 1) x := by sorry

end RevenueManagement
