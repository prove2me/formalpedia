-- Prove2me | Theorems.Thm_RevenueManagement_littlewood_marginal_value
-- name    : RevenueManagement.littlewood_marginal_value
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:28:26.773851+00:00
-- url     : https://prove2.me/theorems/9cb7bb9e-e888-4a59-be04-141991a0adb6
-- title:
--   Littlewood's two-class rule (2.1): the marginal value of the x-th unit is p₁ P(D₁ ≥ x), and a class-2 request is accepted iff p₂ ≥ p₁ P(D₁ ≥ x)
-- statement:
--   In the static model with nonnegative prices and pmf demands, the expected marginal value of
--   the $x$-th unit of capacity at stage 1 is $\Delta V_1(x) = p_1\,\mathbb P(D_1 \ge x)$ for
--   $x \ge 1$, and accepting a single class-2 request when $x$ units remain is stage-optimal if
--   and only if $p_2 \ge p_1\,\mathbb P(D_1 \ge x)$, which is Littlewood's rule (2.1). The book
--   derives it by marginal analysis and calls it a special case of Theorem 2.1.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, Sect. 2.2.1 pp. 35-36, Eq. (2.1) ('the expected gain from reserving the x-th unit for class 1 (the expected marginal value) is p1 P(D1 ≥ x). Therefore, it makes sense to accept a class 2 request as long as its price exceeds this marginal value')

import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem littlewood_marginal_value (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j))
    (hp : ∀ j, 0 ≤ p j) (x : ℕ) (hx : 1 ≤ x) :
    staticDelta p f 1 x = p 1 * ∑' d, (if x ≤ d then f 1 d else 0) ∧
      (IsStageOptimal p f 1 x 1 1 ↔ p 1 * ∑' d, (if x ≤ d then f 1 d else 0) ≤ p 2) := by sorry

end RevenueManagement
