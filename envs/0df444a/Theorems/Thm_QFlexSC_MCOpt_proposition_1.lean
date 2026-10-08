-- Prove2me | Theorems.Thm_QFlexSC_MCOpt_proposition_1
-- name    : QFlexSC.MCOpt.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:12.426684+00:00
-- url     : https://prove2.me/theorems/4d564611-7942-4475-a318-0038c2df4ba8
-- title:
--   Proposition 1, p. 96 — the MC schedule (21)–(23) is optimal for (F-OLFC) and admissible
-- statement:
--   Let a flex node have QF parameters satisfying the standing assumptions $\alpha^{in}_q, \alpha^{out}_q \ge 0$ and $0 \le \omega^{in}_q, \omega^{out}_q \le 1$ ($q \ge 1$), let $G : \mathbb R \to \mathbb R$ be a convex cost function minimized at zero, and fix a horizon $h$. Run the Minimum Commitment policy (21)–(23) from an initial state $(I(0), r(0))$ with $r(0) \ge 0$, against any customer release schedules $\{f(t)\}$ whose updates obey the output IR constraints (6). Then the policy is admissible and optimal:
--   1. **Coverage.** $I(t) \ge 0$ for every $t \ge 1$.
--   2. **Input IR.** For every $t \ge 2$ and $j \ge 0$,
--   $$(1 - \omega^{in}_{j+1})\, r_{j+1}(t-1) \le r_j(t) \le (1 + \alpha^{in}_{j+1})\, r_{j+1}(t-1).$$
--   3. **Optimality.** For every $t \ge 2$, the MC schedule $r(t)$, together with some planned purchases $(r_0(t), \dots, r_0(t+h))$, is feasible for program (F-OLFC) at period $t$ (data $I(t-1)$, $r(t-1)$, $f(t)$), and no feasible point of (F-OLFC) has a smaller objective $\sum_{j=0}^{h} G(I(t+j))$.
--
--   Proposition 1 justifies the MC policy as the open-loop feedback control rule of the flex node: it supports every customer revision the contract allows, respects the node's own contract upstream, and commits to as little future inventory as the open-loop program permits.
--
--   **Formalization Note** Three corrections to the printed statement are disclosed. (i) (F-OLFC)'s constraint (19) is imposed for $j = 0, \dots, h$ instead of the printed $j = 0, \dots, h-1$; with the printed range the optimality claim is false (counterexample with $h = 0$ in the mission description). (ii) Input IR and optimality are claimed from the second MC period on (run periods $t + 1$, $t \ge 1$), since the paper's induction needs $r(t-1)$ to be MC-generated; coverage holds from the first. (iii) $r(0) \ge 0$ is assumed (quantities are nonnegative, p. 95). $I(0)$ and $f$ carry no sign hypothesis. Schedules are infinite sequences, the parameter sequences' index $0$ is unused, and the future purchases are existential because "only $\{r(t)\}$ needs to be provided to the supplier" (p. 97).
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), p. 96, Proposition 1, (17)–(23)

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model
import Definitions.Def_QFlexSC_MCOpt_FOLFC

namespace QFlexSC.MCOpt

theorem proposition_1 (P : QFlexSC.ZeroInv.QFParams) (f : ℕ → ℕ → ℝ) (I₀ : ℝ) (r₀ : ℕ → ℝ) (h : ℕ)
    (G : ℝ → ℝ)
    (hP : ∀ q, 1 ≤ q → 0 ≤ P.αin q ∧ 0 ≤ P.αout q ∧ 0 ≤ P.ωin q ∧ P.ωin q ≤ 1 ∧
      0 ≤ P.ωout q ∧ P.ωout q ≤ 1)
    (hr₀ : ∀ j, 0 ≤ r₀ j) (hf : QFlexSC.ZeroInv.IROut P f)
    (hG : ConvexOn ℝ Set.univ G) (hG0 : ∀ y, G 0 ≤ G y) :
    (∀ t, 1 ≤ t → 0 ≤ QFlexSC.ZeroInv.inv P I₀ r₀ f t) ∧
    ∀ t, 1 ≤ t →
      QFlexSC.ZeroInv.IRIn P (QFlexSC.ZeroInv.sched P I₀ r₀ f) t ∧
      ∃ p, Feasible P h (QFlexSC.ZeroInv.inv P I₀ r₀ f t) (QFlexSC.ZeroInv.sched P I₀ r₀ f t) (f (t+1))
          (QFlexSC.ZeroInv.sched P I₀ r₀ f (t+1)) p ∧
        ∀ x' p', Feasible P h (QFlexSC.ZeroInv.inv P I₀ r₀ f t) (QFlexSC.ZeroInv.sched P I₀ r₀ f t) (f (t+1)) x' p' →
          objective G P h (QFlexSC.ZeroInv.inv P I₀ r₀ f t) (f (t+1)) p ≤
            objective G P h (QFlexSC.ZeroInv.inv P I₀ r₀ f t) (f (t+1)) p' := by sorry

end QFlexSC.MCOpt
