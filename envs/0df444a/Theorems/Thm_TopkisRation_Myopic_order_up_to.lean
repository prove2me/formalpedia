-- Prove2me | Theorems.Thm_TopkisRation_Myopic_order_up_to
-- name    : TopkisRation.Myopic.order_up_to
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:00.355007+00:00
-- url     : https://prove2.me/theorems/7f9232f7-3c1c-40ab-ae7e-1bf7b8a7b210
-- title:
--   §3, p. 175 — ordering to w ∨ x̄ᵐ minimizes period-m cost
-- statement:
--   For each ordering period $m$, the convex actual cost $\widetilde g^{,m}$ attains a minimum at some $\bar x^m\ge0$. Every nonnegative minimizer $x$ yields an optimal order-up-to policy: from net stock $w$, among all feasible order-up-to levels $z\ge w^+$, the level $w\vee x$ minimizes $\widetilde g^{,m}$:
--
--   $$\widetilde g^{,m}(w\vee x)\le\widetilde g^{,m}(z)\qquad(z\ge w^+).$$
--
--   This is the general dynamic ordering policy before the myopic-level condition of Theorem 4 is imposed.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 175, §3, The General Case, paragraph before Myopic Policies

import Definitions.Def_TopkisRation_Myopic_MultiPeriod

namespace TopkisRation.Myopic

variable {n : ℕ}

/-- The General Case, p. 175: `g̃ᵐ` has a minimizer, and ordering to its level is optimal. -/
theorem order_up_to (Q : MultiModel n) (hQ : Q.Standing)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 Q.N) :
    (∃ x : ℝ, 0 ≤ x ∧ ∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) ∧
    ∀ x : ℝ, 0 ≤ x → (∀ z, 0 ≤ z → Q.gtilde m x ≤ Q.gtilde m z) →
      ∀ w z : ℝ, max w 0 ≤ z → Q.gtilde m (max w x) ≤ Q.gtilde m z := by sorry

end TopkisRation.Myopic
