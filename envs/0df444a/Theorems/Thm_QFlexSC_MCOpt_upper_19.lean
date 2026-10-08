-- Prove2me | Theorems.Thm_QFlexSC_MCOpt_upper_19
-- name    : QFlexSC.MCOpt.upper_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:18.816057+00:00
-- url     : https://prove2.me/theorems/57894efe-7ffa-4168-b28d-f26a3a189412
-- title:
--   Appendix 1, p. 108 — the MC schedule obeys the upper bound of (19): $r_j(t) \le (1+\alpha^{in}_{j+1})\, r_{j+1}(t-1)$
-- statement:
--   Consider the rolling run of the Minimum Commitment policy from an initial state $(I(0), r(0))$ with $r(0) \ge 0$, under the standing assumptions $\alpha^{in}_q, \alpha^{out}_q \ge 0$ and $0 \le \omega^{in}_q, \omega^{out}_q \le 1$ ($q \ge 1$), and suppose every update of the customer's schedule obeys the output IR constraints (6). Then for every period $t \ge 2$ and every $j \ge 0$,
--   $$r_j(t) \ \le\ (1 + \alpha^{in}_{j+1})\, r_{j+1}(t-1).$$
--
--   Together with the lower bound built into (21), this is the replenishment-side half of admissibility: the schedule the node passes upstream respects its own contract with the supplier.
--
--   **Formalization Note** The run's period $t + 1$ with $t \ge 1$ is the paper's period $t \ge 2$, the first period whose predecessor schedule was itself MC-generated; at the first MC period the claim fails from an arbitrary $r(0)$. The hypothesis $r(0) \ge 0$ is added (quantities are measured in end-item equivalents, p. 95): with $r_{j+1}(t-1) < 0$ and $\alpha^{in} > 0$ the two bounds of (19) cross.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), Appendix 1, proof of Proposition 1, p. 108

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model

namespace QFlexSC.MCOpt

theorem upper_19 (P : QFlexSC.ZeroInv.QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ)
    (hP : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hr₀ : ∀ j, 0 ≤ r₀ j) (hf : QFlexSC.ZeroInv.IROut P f) :
    ∀ t, 1 ≤ t → ∀ j,
      QFlexSC.ZeroInv.sched P I₀ r₀ f (t+1) j ≤ (1 + P.αin (j+1)) * QFlexSC.ZeroInv.sched P I₀ r₀ f t (j+1) := by sorry

end QFlexSC.MCOpt
