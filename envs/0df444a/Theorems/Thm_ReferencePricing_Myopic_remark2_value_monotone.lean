-- Prove2me | Theorems.Thm_ReferencePricing_Myopic_remark2_value_monotone
-- name    : ReferencePricing.Myopic.remark2_value_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T09:35:04.40042+00:00
-- url     : https://prove2.me/theorems/5ed526a2-c2f0-4b0d-b973-e1892a329323
-- title:
--   Remark 2 — the value function V(r) is increasing in the reference price r
-- statement:
--   Let $P = [0, \bar p]$ with $\bar p > 0$, $\alpha \in [0, 1)$, $\beta \in (0, 1)$, and let demand $D(p,r) = d(p) + R(r-p, r)$ satisfy Assumption 1 with $R(0, r) = 0$. Let $V$ be the value function of the problem with profit $\Pi(p, r) = p\,D(p, r)$. Then $V$ is increasing on $P$:
--   $$r, r' \in P,\ r \le r' \implies V(r) \le V(r').$$
--
--   Higher reference prices are better for the firm. This is the input to the comparison of the optimal and myopic policies (Proposition 1).
--
--   **Formalization Note.** Remark 2 sits in §3, where only Assumption 1 is standing, so Assumptions 2 and 3 are not hypotheses here. $R(0,r)=0$ is part of the model (the definition of $R$).
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 417, Remark 2

import Mathlib
import Definitions.Def_ReferencePricing_Myopic_Assumptions
import Definitions.Def_ReferencePricing_Myopic_value

namespace ReferencePricing.Myopic

/-- Remark 2 (p. 417): under Assumption 1, the value function `V(r)` is an increasing function of
the reference price `r` on `P = [0, p̄]`. -/
theorem remark2_value_monotone (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ) (α β pbar : ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hR0 : ∀ r, R 0 r = 0) (hA1 : Assumption1 d R pbar) :
    MonotoneOn (value (profit d R) α β pbar) (Set.Icc 0 pbar) := by sorry

end ReferencePricing.Myopic
