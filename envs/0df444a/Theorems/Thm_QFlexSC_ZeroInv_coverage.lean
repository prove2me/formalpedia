-- Prove2me | Theorems.Thm_QFlexSC_ZeroInv_coverage
-- name    : QFlexSC.ZeroInv.coverage
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:59.617812+00:00
-- url     : https://prove2.me/theorems/083e22ee-f15d-477b-89c2-f5198a8c378d
-- title:
--   Appendix 1, proof of Proposition 1, p. 108 — the MC schedule satisfies r_j(t) ≥ T_j(t), hence I(t) ≥ 0
-- statement:
--   Consider a flex node running the Minimum Commitment (MC) policy (21)–(23) from an arbitrary initial state $(I(0), r(0))$ against arbitrary release schedules $f(t)$ and arbitrary QF parameters. For every period $t \ge 1$:
--
--   1. for every $j \ge 0$, the replenishment schedule dominates the target (22),
--   $$r_j(t) \ge T_j(t) = \frac{(1 + A^{out}_j) f_j(t) - l_j(t)}{1 + A^{in}_j};$$
--   2. the ending stock is nonnegative,
--   $$I(t) = I(t-1) + r_0(t) - f_0(t) \ge 0 .$$
--
--   Part 2 follows from part 1 at $j = 0$, where $A_0 = 0$ and $l_0(t) = I(t-1)$ give $T_0(t) = f_0(t) - I(t-1)$. This is the coverage half of the admissibility of the MC policy: the node never fails to cover its customer's actual purchase.
--
--   **Formalization Note.** No hypothesis on the data is needed; the statement is about the run of the model's MC policy, and $l_j(t)$ is the projection computed in period $t$ from $(I(t-1), r(t-1), f(t))$.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), p. 108, Appendix 1, proof of Proposition 1

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

namespace QFlexSC.ZeroInv

theorem coverage (P : QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ) :
    ∀ t : ℕ, 1 ≤ t →
      (∀ j : ℕ, target P (f t) (projInvAt P I₀ r₀ f t j) j ≤ sched P I₀ r₀ f t j) ∧
        0 ≤ inv P I₀ r₀ f t := by sorry

end QFlexSC.ZeroInv
