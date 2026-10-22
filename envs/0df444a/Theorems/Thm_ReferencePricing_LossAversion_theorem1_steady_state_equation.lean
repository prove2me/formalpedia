-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_theorem1_steady_state_equation
-- name    : ReferencePricing.LossAversion.theorem1_steady_state_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:50:00.613693+00:00
-- url     : https://prove2.me/theorems/63d81827-a908-4eb3-8c5f-4aaa31806599
-- title:
--   Theorem 1 (first sentence) — a steady state is the unique solution of $\pi'(p)/(1-\beta)=p\lambda(p)/(1-\alpha\beta)$
-- statement:
--   Consider the loss-neutral problem (2) on $P=[0,\bar p]$ with $\alpha\in[0,1)$ and $\beta\in(0,1)$, under Assumptions 1–3 and with $d$ differentiable. Write $\pi(p)=p\,d(p)$ for the base profit and $\lambda(r)=R_x(0,r)$ for the slope of the reference effect. If $p^{**}$ is a steady state of (2), then $p^{**}$ solves
--   $$
--   \frac{\pi'(p)}{1-\beta}=\frac{p\,\lambda(p)}{1-\alpha\beta},\tag{3}
--   $$
--   and every $q\in P$ solving (3) equals $p^{**}$.
--
--   Equation (3) characterizes the long-run price. It is used for the comparative statics of steady states (Remark 3) and for the loss-averse case, where the steady states of the problems $(P_\theta)$ are located through it.
--
--   **Formalization Note** Only the first sentence of Theorem 1 is formalized. The comparative statics in $\alpha$, $\beta$ and the bounds $p^{M*}\le p^{**}\le\tilde p$ are not part of this item. Uniqueness is among solutions in $P$. The hypothesis that $d$ is differentiable is added, because $\pi'$ appears in (3).
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 418, Theorem 1, first sentence, Eq. (3) (proof in Appendix A.2, p. 425)

import Mathlib
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_RobustBooking_Shared_Assumptions
open RobustBooking.Shared

namespace ReferencePricing.LossAversion

/-- Theorem 1 (Steady State), first sentence, Popescu and Wu 2007, p. 418: under Assumptions 1–3,
if problem (2) admits a steady state `p**`, then `p**` solves (3),
`π′(p) / (1 − β) = p λ(p) / (1 − αβ)`, and it is the only solution of (3) in `P = [0, p̄]`. -/
theorem theorem1_steady_state_equation (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : Differentiable ℝ d) (hA1 : Assumption1 pbar d R) (hA2 : Assumption2 R)
    (hA3 : Assumption3 pbar d R)
    (p : ℝ) (hp : IsSteadyState (profit d R) α β pbar p) :
    deriv (baseProfit d) p / (1 - β) = p * refSlope R p / (1 - α * β) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) pbar,
        deriv (baseProfit d) q / (1 - β) = q * refSlope R q / (1 - α * β) → q = p := by sorry

end ReferencePricing.LossAversion
