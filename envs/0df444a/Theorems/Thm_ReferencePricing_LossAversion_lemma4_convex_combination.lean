-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_lemma4_convex_combination
-- name    : ReferencePricing.LossAversion.lemma4_convex_combination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:52:13.813666+00:00
-- url     : https://prove2.me/theorems/09c5d6c1-522d-4403-92d7-cfeafc437bc5
-- title:
--   Lemma 4 — $(P_\theta)$ satisfies Assumptions 1–3, $V_\theta\ge V_K$, and steady states of $(P_\theta)$ are steady states of $(K)$
-- statement:
--   Consider the loss-averse pricing problem on $P=[0,\bar p]$ with $\alpha\in[0,1)$ and $\beta\in(0,1)$. The base demand $d$ is differentiable, and $R_G,R_L$ are gain and loss reference effects satisfying Assumptions 4 and 5. Assumption 1 holds for the kinked demand $d(p)+R_K(r-p,r)$ and for the smooth demands $d(p)+R_G(r-p,r)$ and $d(p)+R_L(r-p,r)$. Let $(K)$ be the problem with profit $\Pi_K(p,r)=p\,(d(p)+R_K(r-p,r))$, and $(P_\theta)$ the problem with profit $\Pi_\theta(p,r)=p\,(d(p)+R_\theta(r-p,r))$ for $R_\theta=\theta R_G+(1-\theta)R_L$. Then, for every $\theta\in[0,1]$:
--
--   1. the pair $(d,R_\theta)$ satisfies Assumptions 1, 2 and 3;
--   2. the value functions satisfy
--   $$
--   V_\theta(r)\ge V_K(r)\qquad\text{for all } r\in P;
--   $$
--   3. every steady state of $(P_\theta)$ is a steady state of $(K)$.
--
--   The smooth problems $(P_\theta)$ bound the kinked problem from above. This lets the loss-neutral theory (Theorems 1 and 2) produce steady states of the kinked problem.
--
--   **Formalization Note** The paper states $V_\theta(r)\ge V_K(r)$ "for all $r$". The value functions are only meaningful for reference prices in $P$, so the inequality is stated on $P$. Assumption 1 for the demands of $R_G$ and $R_L$ is an added hypothesis: the paper's proof speaks of "reference effects satisfying Assumptions 1–5", while Assumption 5 as printed only gives Assumption 3. Differentiability of $d$ is added as in Theorem 1. Steady states use the paper's largest-maximizer policy in both problems.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 422, Lemma 4 (proof in Appendix A.10, p. 428)

import Mathlib
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_ReferencePricing_LossAversion_Kinked
open RobustBooking.Shared

namespace ReferencePricing.LossAversion

/-- Lemma 4, Popescu and Wu 2007, p. 422: under Assumptions 1, 4, 5, for every `θ ∈ [0, 1]` the
problem (P_θ) with reference effect `R_θ = θ R_G + (1 − θ) R_L` satisfies Assumptions 1–3; its value
function dominates that of the kinked problem (K), `V_θ(r) ≥ V_K(r)` on `P`; and every steady
state of (P_θ) is a steady state of (K). -/
theorem lemma4_convex_combination (pbar α β : ℝ) (d : ℝ → ℝ) (RG RL : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : Differentiable ℝ d)
    (hA1K : Assumption1 pbar d (RK RG RL))
    (hA1G : Assumption1 pbar d RG) (hA1L : Assumption1 pbar d RL)
    (hA4 : Assumption4 pbar RG RL) (hA5 : Assumption5 pbar d RG RL)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) :
    (Assumption1 pbar d (Rtheta RG RL θ) ∧ Assumption2 (Rtheta RG RL θ) ∧
        Assumption3 pbar d (Rtheta RG RL θ)) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) pbar,
        value (profit d (RK RG RL)) α β pbar r ≤ value (profit d (Rtheta RG RL θ)) α β pbar r) ∧
      (∀ p : ℝ, IsSteadyState (profit d (Rtheta RG RL θ)) α β pbar p →
        IsSteadyState (profit d (RK RG RL)) α β pbar p) := by sorry

end ReferencePricing.LossAversion
