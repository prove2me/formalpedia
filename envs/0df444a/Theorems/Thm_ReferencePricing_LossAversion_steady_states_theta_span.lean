-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_steady_states_theta_span
-- name    : ReferencePricing.LossAversion.steady_states_theta_span
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:52:26.318033+00:00
-- url     : https://prove2.me/theorems/4808a4eb-fa8c-4883-99ae-6192cc2f7b76
-- title:
--   §5.2 — $p^{**}_L\le p^{**}_\theta\le p^{**}_G$, and the steady states $p^{**}_\theta$ span $[p^{**}_L,p^{**}_G]$
-- statement:
--   Work under the hypotheses of Lemma 4: $P=[0,\bar p]$, $\alpha\in[0,1)$, $\beta\in(0,1)$, $d$ differentiable, Assumptions 4 and 5 for $(R_G,R_L)$, and Assumption 1 for the kinked, gain and loss demands. Let $p^{**}_L$ be a steady state of the loss problem $(P_L)$ (reference effect $R_L$) and $p^{**}_G$ a steady state of the gain problem $(P_G)$ (reference effect $R_G$). For $\theta\in[0,1]$ let $(P_\theta)$ be the problem with reference effect $R_\theta=\theta R_G+(1-\theta)R_L$. Then:
--
--   1. $p^{**}_L\le p^{**}_G$;
--   2. for every $\theta\in[0,1]$, every steady state $p^{**}_\theta$ of $(P_\theta)$ satisfies
--   $$
--   p^{**}_L\le p^{**}_\theta\le p^{**}_G ;
--   $$
--   3. every $p\in[p^{**}_L,p^{**}_G]$ is a steady state of $(P_\theta)$ for some $\theta\in[0,1]$.
--
--   Together with Lemma 4, this shows that every point of $[p^{**}_L,p^{**}_G]$ is a steady state of the kinked problem.
--
--   **Formalization Note** The appendix proof writes the steady-state equation of $(P_\theta)$ with weights $p(\theta\lambda_L(p)+(1-\theta)\lambda_G(p))$. These are swapped relative to the definition (8), in which $\theta$ weighs $R_G$. The span claim is the same either way; this item uses the weights of (8).
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 422, Section 5.2, paragraph after Lemma 4 (proof in Appendix A.11, third paragraph, p. 428)

import Mathlib
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_ReferencePricing_LossAversion_Kinked
open RobustBooking.Shared

namespace ReferencePricing.LossAversion

/-- Popescu and Wu 2007, §5.2, p. 422 (paragraph after Lemma 4; proof §A.11, p. 428): under
Assumptions 1, 4, 5, if `p**_L` and `p**_G` are steady states of (P_L) and (P_G), then
`p**_L ≤ p**_G`, every steady state `p**_θ` of (P_θ), `θ ∈ [0, 1]`, satisfies
`p**_L ≤ p**_θ ≤ p**_G`, and as `θ` ranges over `[0, 1]` the steady states `p**_θ` span
`[p**_L, p**_G]`: every point of that interval is a steady state of some (P_θ). -/
theorem steady_states_theta_span (pbar α β : ℝ) (d : ℝ → ℝ) (RG RL : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : Differentiable ℝ d)
    (hA1K : Assumption1 pbar d (RK RG RL))
    (hA1G : Assumption1 pbar d RG) (hA1L : Assumption1 pbar d RL)
    (hA4 : Assumption4 pbar RG RL) (hA5 : Assumption5 pbar d RG RL)
    (pL pG : ℝ) (hpL : IsSteadyState (profit d RL) α β pbar pL)
    (hpG : IsSteadyState (profit d RG) α β pbar pG) :
    pL ≤ pG ∧
      (∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ p : ℝ,
        IsSteadyState (profit d (Rtheta RG RL θ)) α β pbar p → p ∈ Set.Icc pL pG) ∧
      ∀ p ∈ Set.Icc pL pG, ∃ θ ∈ Set.Icc (0 : ℝ) 1,
        IsSteadyState (profit d (Rtheta RG RL θ)) α β pbar p := by sorry

end ReferencePricing.LossAversion
