-- Prove2me | Theorems.Thm_QFlexSC_MCOpt_eq_30_relaxed_optimal
-- name    : QFlexSC.MCOpt.eq_30_relaxed_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:02.402103+00:00
-- url     : https://prove2.me/theorems/23c998e3-8ebb-44cf-a112-04f908862a75
-- title:
--   (30)–(31), pp. 107–108 — $r_0^*$ is optimal for (F-OLFC) with the upper bounds of (19)–(20) relaxed
-- statement:
--   Fix one period's data: a horizon $h$, the stock $I(t-1)$, the previous replenishment schedule $r(t-1)$ and the release schedule $f(t)$, all arbitrary real numbers, and input parameters with $0 \le \omega^{in}_q \le 1$ ($q \ge 1$). Let $G : \mathbb R \to \mathbb R$ be convex and minimized at $0$. Consider the relaxed program: minimize $\sum_{j=0}^{h} G(I(t+j))$ subject to (17), (18) and the lower bounds
--   $$(1 - \omega^{in}_{j+1})\, r_{j+1}(t-1) \le r_j(t), \qquad (1 - \Omega^{in}_j)\, r_j(t) \le r_0(t+j), \qquad j = 0, \dots, h.$$
--   Then the purchases $r_0^*(t+j)$ of (30)–(31),
--   $$r_0^*(t+j) = \max\big\{(1 + A^{out}_j) f_j(t) - \bar l_j(t),\ (1 - \Omega^{in}_{j+1})\, r_{j+1}(t-1)\big\},$$
--   with $\bar l_0(t) = I(t-1)$ and $\bar l_j(t) = \bar l_{j-1}(t) + r_0^*(t+j-1) - (1 + A^{out}_{j-1}) f_{j-1}(t)$, are attainable by some schedule $r(t)$ of the relaxed program, and no feasible point of the relaxed program has a smaller objective.
--
--   This is the first step of the paper's solution of (F-OLFC): an MRP-style lot-for-lot rule with minimum lot sizes.
--
--   **Formalization Note** The conclusion is stated as feasibility of $r_0^*$ (for some schedule) plus a lower bound on the objective of every feasible point, not as an infimum. The program ranges over all real schedules and purchases.
-- source:
--   Tsay & Lovejoy, Quantity flexibility contracts and supply chain performance, MSOM 1(2) (1999), Appendix 1, proof of Proposition 1, pp. 107–108, (30)–(31)

import Mathlib
import Definitions.Def_QFlexSC_ZeroInv_Model
import Definitions.Def_QFlexSC_MCOpt_FOLFC

namespace QFlexSC.MCOpt

theorem eq_30_relaxed_optimal (P : QFlexSC.ZeroInv.QFParams) (h : ℕ) (Iprev : ℝ) (rprev f : ℕ → ℝ)
    (G : ℝ → ℝ)
    (hω : ∀ q, 1 ≤ q → 0 ≤ P.ωin q ∧ P.ωin q ≤ 1)
    (hG : ConvexOn ℝ Set.univ G) (hG0 : ∀ y, G 0 ≤ G y) :
    (∃ x, RelaxedFeasible P h Iprev rprev f x (pStar P Iprev rprev f)) ∧
    ∀ x' p', RelaxedFeasible P h Iprev rprev f x' p' →
      objective G P h Iprev f (pStar P Iprev rprev f) ≤ objective G P h Iprev f p' := by sorry

end QFlexSC.MCOpt
