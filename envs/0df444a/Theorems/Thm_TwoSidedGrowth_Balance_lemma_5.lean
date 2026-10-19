-- Prove2me | Theorems.Thm_TwoSidedGrowth_Balance_lemma_5
-- name    : TwoSidedGrowth.Balance.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:20.443986+00:00
-- url     : https://prove2.me/theorems/c0d3bba9-6612-48ca-afc3-719856929e7b
-- title:
--   Lemma 5, p. 41 — along an admissible size path the discounted profit equals ∫_0^T e^{−ρt}G dt − e^{−ρT}x(T) + x(0)
-- statement:
--   Consider the two-sided growth model in size-balance form, with output $g(\gamma,x)=x^{\alpha}h(\gamma)$, net welfare rate $G(\gamma,x)=(v-c)g(\gamma,x)-(\rho+\beta^s_0\gamma+\beta^d_0(1-\gamma))x$, and discount rate $\rho$. Let $T\ge 0$ and let $(x,\gamma,\pi)$ be a size path, a balance path and a margin path on $[0,T]$ that are admissible: $x>0$, $0\le\gamma\le 1$, $\gamma$ and $\pi$ continuous, and $x$ continuously differentiable and obeying the state equation (12). Then
--   $$\int_0^T e^{-\rho t}\,\pi\,g(\gamma,x)\,dt=\int_0^T e^{-\rho t}\,G(\gamma,x)\,dt-e^{-\rho T}x(T)+x(0).$$
--
--   The identity removes the margin $\pi$ from the objective of (13): the platform's discounted profit along a trajectory depends on the balance only through the net welfare rate $G$. This is what reduces the choice of the balance to a pointwise maximization of $G(\cdot,x)$.
--
--   **Formalization Note.** The paper's "finite trajectory" is an admissible triple on $[0,T]$ as defined in the mission's setting; the standing assumptions of §3 are hypotheses.
-- source:
--   Lian, van Ryzin, Optimal Growth in Two-Sided Markets, SSRN working paper 3310559 (version of 2020-01-16), p. 41, Lemma 5

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Setting

namespace TwoSidedGrowth.Balance
theorem lemma_5 (M : Model) (hM : M.Standing) (T : ℝ) (x γ pm : ℝ → ℝ)
    (hadm : Admissible M T x γ pm) :
    profit M T x γ pm =
      (∫ t in (0:ℝ)..T, Real.exp (-(M.ρ * t)) * G M (γ t) (x t))
        - Real.exp (-(M.ρ * T)) * x T + x 0 := by sorry
end TwoSidedGrowth.Balance
