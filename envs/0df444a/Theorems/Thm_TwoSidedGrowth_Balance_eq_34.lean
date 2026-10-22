-- Prove2me | Theorems.Thm_TwoSidedGrowth_Balance_eq_34
-- name    : TwoSidedGrowth.Balance.eq_34
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:26.41606+00:00
-- url     : https://prove2.me/theorems/bf80bf92-e7bc-4242-8541-787c9cd45cef
-- title:
--   (34), p. 43 — where the optimal balance is interior it is differentiable in x with dγ*/dx = (β^s_0 − β^d_0)(1 − α)/((v − c)h″(γ*)x^α)
-- statement:
--   In the two-sided growth model under its standing assumptions, let $\gamma^*$ be any function that assigns to every market size $x>0$ a balance satisfying the clamp formula (14). If at some $x>0$ the balance $\gamma^*(x)$ is interior, $0<\gamma^*(x)<1$, then $\gamma^*$ is differentiable at $x$ with
--   $$\frac{d\gamma^*(x)}{dx}=\frac{(\beta^s_0-\beta^d_0)(1-\alpha)}{(v-c)\,h''(\gamma^*(x))\,x^{\alpha}},$$
--   and, since $h''<0$,
--   $$\operatorname{sgn}\Bigl(\frac{d\gamma^*(x)}{dx}\Bigr)=\operatorname{sgn}\bigl((\alpha-1)(\beta^s_0-\beta^d_0)\bigr).\tag{34}$$
--
--   The sign rule says in which direction the optimal balance moves as the market grows: it depends only on the returns to scale ($\alpha$ versus $1$) and on which side is more durable ($\beta^s_0$ versus $\beta^d_0$).
--
--   **Formalization Note.** The printed $h''(\gamma)$ is $h''$ evaluated at $\gamma^*(x)$. Differentiability of $\gamma^*$ is a conclusion, not a hypothesis.
-- source:
--   Lian, van Ryzin, Optimal Growth in Two-Sided Markets, SSRN working paper 3310559 (version of 2020-01-16), p. 43, display (34) and the derivative before it, in the proof of Lemma 6

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Setting

namespace TwoSidedGrowth.Balance
theorem eq_34 (M : Model) (hM : M.Standing) (γs : ℝ → ℝ)
    (hγs : ∀ x : ℝ, 0 < x → IsBalance M x (γs x)) (x : ℝ) (hx : 0 < x)
    (hint : γs x ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt γs
      ((M.bs0 - M.bd0) * (1 - M.α) /
        ((M.v - M.c) * deriv (deriv (h M)) (γs x) * x ^ M.α)) x ∧
    SignType.sign ((M.bs0 - M.bd0) * (1 - M.α) /
        ((M.v - M.c) * deriv (deriv (h M)) (γs x) * x ^ M.α)) =
      SignType.sign ((M.α - 1) * (M.bs0 - M.bd0)) := by sorry
end TwoSidedGrowth.Balance
