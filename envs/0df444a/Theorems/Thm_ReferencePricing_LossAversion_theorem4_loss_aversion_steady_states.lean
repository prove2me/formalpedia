-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_theorem4_loss_aversion_steady_states
-- name    : ReferencePricing.LossAversion.theorem4_loss_aversion_steady_states
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:52:57.597686+00:00
-- url     : https://prove2.me/theorems/767aae5e-2a09-4d82-aec2-ffe6968e2134
-- title:
--   Theorem 4 — under loss aversion the steady states form $[p^{**}_L,p^{**}_G]$ and optimal paths converge monotonically to the nearer endpoint
-- statement:
--   A monopolist charges prices $p_t\in P=[0,\bar p]$ ($\bar p>0$) to consumers whose reference price evolves as $r_{t+1}=\alpha r_t+(1-\alpha)p_t$, with $\alpha\in[0,1)$. The firm maximizes discounted profit with discount factor $\beta\in(0,1)$. Demand is $D(p,r)=d(p)+R_K(r-p,r)$, where $d$ is a differentiable base demand. The kinked reference effect $R_K$ equals a gain effect $R_G$ for $x=r-p\ge 0$ and a loss effect $R_L$ for $x<0$, and satisfies Assumption 4 (twice differentiable components, increasing in $x$, $R_G-R_L$ single crossing, loss aversion $\lambda_L(r)>\lambda_G(r)$) and Assumption 5 (the gain and loss profits satisfy Assumption 3). Assumption 1 holds for the kinked demand and for the gain and loss demands $d(p)+R_G(r-p,r)$ and $d(p)+R_L(r-p,r)$. Call $(K)$ the kinked problem, and $(P_L)$, $(P_G)$ the smooth problems with reference effects $R_L$, $R_G$.
--
--   Then there are prices $p^{**}_L$ and $p^{**}_G$ such that:
--
--   1. $p^{**}_L$ is the unique steady state of $(P_L)$ and $p^{**}_G$ the unique steady state of $(P_G)$, and $p^{**}_L\le p^{**}_G$;
--   2. the set of steady states of $(K)$ is exactly
--   $$
--   \{\,r : r \text{ is a steady state of }(K)\,\}=[p^{**}_L,\,p^{**}_G];
--   $$
--   3. for $r_0\in[p^{**}_L,p^{**}_G]$ the optimal price path of $(K)$ is constant, $p^*_t=r_0$ for all $t$;
--   4. for $r_0\in P$ with $r_0<p^{**}_L$, the optimal reference price path $r^*_t$ of $(K)$ is nondecreasing and converges to $p^{**}_L$, and the optimal price path $p^*_t$ converges to $p^{**}_L$;
--   5. for $r_0\in P$ with $r_0>p^{**}_G$, the optimal reference price path of $(K)$ is nonincreasing and converges to $p^{**}_G$, and the optimal price path converges to $p^{**}_G$.
--
--   Under loss aversion a whole interval of prices is self-sustaining. A firm starting inside it keeps its price, and one starting outside it moves monotonically to the nearer endpoint.
--
--   **Formalization Note** Optimal policies are the largest maximizers of the Bellman objective and steady states are fixed points of that policy, as in the paper. $p^{**}_L$ and $p^{**}_G$ are existentially quantified together with their uniqueness, so the theorem also asserts that these steady states exist. The page prints "$r_0>p^*_G$", a typo for $p^{**}_G$. Two hypotheses are added: differentiability of $d$, because Assumption 3(b) uses $\pi'$; and Assumption 1 for the gain and loss demands, which the paper's proof of Lemma 4 uses.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 422, Theorem 4 (proof in Appendix A.11, p. 428)

import Mathlib
import Definitions.Def_RobustBooking_Shared_optPrice
import Definitions.Def_ReferencePricing_LossAversion_Kinked
open RobustBooking.Shared

open Filter Topology

namespace ReferencePricing.LossAversion

/-- Theorem 4 (Steady State, Stability, and Monotonicity Under Loss Aversion), Popescu and Wu 2007,
p. 422. Under Assumptions 1, 4, 5 the loss problem (P_L) and the gain problem (P_G) have unique
steady states `p**_L`, `p**_G` with `p**_L ≤ p**_G`; the set of steady states of the kinked
problem (K) equals `[p**_L, p**_G]`; from `r₀ ∈ [p**_L, p**_G]` the optimal price path of (K) is
constant `p*_t = r₀`; from `r₀ < p**_L` (resp. `r₀ > p**_G`, the page prints `p*_G`) the state
path of (K) converges monotonically to `p**_L` (resp. `p**_G`), and so does the price path. -/
theorem theorem4_loss_aversion_steady_states (pbar α β : ℝ) (d : ℝ → ℝ) (RG RL : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hd : Differentiable ℝ d)
    (hA1K : Assumption1 pbar d (RK RG RL))
    (hA1G : Assumption1 pbar d RG) (hA1L : Assumption1 pbar d RL)
    (hA4 : Assumption4 pbar RG RL) (hA5 : Assumption5 pbar d RG RL) :
    ∃ pL pG : ℝ,
      (∀ r : ℝ, IsSteadyState (profit d RL) α β pbar r ↔ r = pL) ∧
      (∀ r : ℝ, IsSteadyState (profit d RG) α β pbar r ↔ r = pG) ∧
      pL ≤ pG ∧
      {r : ℝ | IsSteadyState (profit d (RK RG RL)) α β pbar r} = Set.Icc pL pG ∧
      (∀ r₀ ∈ Set.Icc pL pG, ∀ t : ℕ, pricePath (profit d (RK RG RL)) α β pbar r₀ t = r₀) ∧
      (∀ r₀ ∈ Set.Icc (0 : ℝ) pbar, r₀ < pL →
        Monotone (statePath (profit d (RK RG RL)) α β pbar r₀) ∧
        Tendsto (statePath (profit d (RK RG RL)) α β pbar r₀) atTop (𝓝 pL) ∧
        Tendsto (pricePath (profit d (RK RG RL)) α β pbar r₀) atTop (𝓝 pL)) ∧
      (∀ r₀ ∈ Set.Icc (0 : ℝ) pbar, pG < r₀ →
        Antitone (statePath (profit d (RK RG RL)) α β pbar r₀) ∧
        Tendsto (statePath (profit d (RK RG RL)) α β pbar r₀) atTop (𝓝 pG) ∧
        Tendsto (pricePath (profit d (RK RG RL)) α β pbar r₀) atTop (𝓝 pG)) := by sorry

end ReferencePricing.LossAversion
