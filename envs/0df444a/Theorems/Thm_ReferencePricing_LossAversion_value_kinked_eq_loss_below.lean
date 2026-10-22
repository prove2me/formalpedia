-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_value_kinked_eq_loss_below
-- name    : ReferencePricing.LossAversion.value_kinked_eq_loss_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:52:36.57924+00:00
-- url     : https://prove2.me/theorems/7712ce19-2785-47e2-afc9-d9a6ec7f6138
-- title:
--   §A.11 — below $p^{**}_L$ the kinked problem and the loss problem have the same value, $V_K(r_0)=V_L(r_0)$
-- statement:
--   Work under the hypotheses of Lemma 4: $P=[0,\bar p]$, $\alpha\in[0,1)$, $\beta\in(0,1)$, $d$ differentiable, Assumptions 4 and 5 for $(R_G,R_L)$, and Assumption 1 for the kinked, gain and loss demands. Let $p^{**}_L$ be a steady state of the loss problem $(P_L)$, the problem with reference effect $R_L$. Then for every initial reference price $r_0\in P$ with $r_0<p^{**}_L$,
--   $$
--   V_K(r_0)=V_L(r_0),
--   $$
--   where $V_K$ and $V_L$ are the value functions of the kinked problem $(K)$ and of $(P_L)$.
--
--   Below the loss steady state, the kinked problem behaves exactly like the smooth loss problem. This transfers the monotone convergence of Theorem 2 for $(P_L)$ to $(K)$ and gives the first part of Theorem 4.
--
--   **Formalization Note** The mirror statement for $r_0>p^{**}_G$ and the gain problem $(P_G)$, which the paper proves "similarly", is not a separate item.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 428, Appendix A.11 (Proof of Theorem 4), first paragraph

import Mathlib
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_ReferencePricing_LossAversion_Kinked
open RobustBooking.Shared

namespace ReferencePricing.LossAversion

/-- Popescu and Wu 2007, §A.11, first paragraph, p. 428: under Assumptions 1, 4, 5, if `p**_L`
is the steady state of (P_L), then for every initial reference price `r₀ ∈ P` below it the
kinked problem (K) and the loss problem (P_L) have the same value, `V_L(r₀) = V_K(r₀)`. -/
theorem value_kinked_eq_loss_below (pbar α β : ℝ) (d : ℝ → ℝ) (RG RL : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : Differentiable ℝ d)
    (hA1K : Assumption1 pbar d (RK RG RL))
    (hA1G : Assumption1 pbar d RG) (hA1L : Assumption1 pbar d RL)
    (hA4 : Assumption4 pbar RG RL) (hA5 : Assumption5 pbar d RG RL)
    (pL : ℝ) (hpL : IsSteadyState (profit d RL) α β pbar pL) :
    ∀ r₀ ∈ Set.Icc (0 : ℝ) pbar, r₀ < pL →
      value (profit d (RK RG RL)) α β pbar r₀ = value (profit d RL) α β pbar r₀ := by sorry

end ReferencePricing.LossAversion
