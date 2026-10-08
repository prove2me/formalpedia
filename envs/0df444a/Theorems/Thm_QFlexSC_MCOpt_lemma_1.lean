-- Prove2me | Theorems.Thm_QFlexSC_MCOpt_lemma_1
-- name    : QFlexSC.MCOpt.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:32.554108+00:00
-- url     : https://prove2.me/theorems/229cc79a-e9bd-4bb8-a01d-dbe7296f4421
-- title:
--   Lemma 1, p. 108 — under the MC policy, $l_j(t) \ge l_{j+1}(t-1)$ for all $j \ge 0$
-- statement:
--   Consider the rolling run of the Minimum Commitment policy with QF parameters satisfying the standing assumptions $\alpha^{in}_q, \alpha^{out}_q \ge 0$ and $0 \le \omega^{in}_q, \omega^{out}_q \le 1$ ($q \ge 1$). Let $t - 1$ and $t$ be two consecutive periods in which the MC policy acts, and write $l_j(t)$ for the projected inventories (23). Suppose
--   1. $I(t-1) \ge 0$, and
--   2. the customer's update from $f(t-1)$ to $f(t)$ obeys the upside of the output IR constraints: $f_j(t) \le (1 + \alpha^{out}_{j+1})\, f_{j+1}(t-1)$ for all $j \ge 0$.
--
--   Then
--   $$l_j(t) \ \ge\ l_{j+1}(t-1) \qquad \text{for all } j \ge 0 .$$
--
--   The projection made at period $t-1$ of the inventory at period $t+j$ is the most conservative one; one period's revisions cannot push it lower. Lemma 1 is the step of the admissibility proof that lets the upper bound of (19) be verified.
--
--   **Formalization Note** The paper's hypothesis (c), that the MC schedule obeys the downside of the input IR constraints, holds by construction in the run (the max in (21)), so it is not a hypothesis. The paper's periods $t-1, t$ are the run's periods $t, t+1$ with $t \ge 1$, so both schedules are MC-generated; `projInvAt` is $l(\cdot)$.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), p. 108, Lemma 1

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

namespace QFlexSC.MCOpt

theorem lemma_1 (P : QFlexSC.ZeroInv.QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ)
    (hP : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (t : ℕ) (ht : 1 ≤ t)
    (ha : 0 ≤ QFlexSC.ZeroInv.inv P I₀ r₀ f t)
    (hb : ∀ j, f (t+1) j ≤ (1 + P.αout (j+1)) * f t (j+1)) :
    ∀ j, QFlexSC.ZeroInv.projInvAt P I₀ r₀ f t (j+1) ≤ QFlexSC.ZeroInv.projInvAt P I₀ r₀ f (t+1) j := by sorry

end QFlexSC.MCOpt
