-- Prove2me | Theorems.Thm_ResetInventory_proposition_5_four_stage_policy
-- name    : ResetInventory.proposition_5_four_stage_policy
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:33.016205+00:00
-- url     : https://prove2.me/theorems/7a3ca589-11da-4694-91af-15b986784cb6
-- title:
--   Proposition 5 — an optimal policy has the four-stage threshold structure
-- statement:
--   **Proposition 5.** Let $c_{\max}\ge0$, $c,K\ge0$ and $0\le\gamma<1$. Let A2 and A3 hold for $t=0,\dots,k-1$ and A5 hold (constants $L,P$). Let $J$ solve the dynamic programming equations (22), and suppose that for every $t=0,\dots,k-1$ the function $J(\cdot,t+1)$ is continuous and piecewise $C^1$ on $[0,c_{\max}]$ with derivative bound $M_{t+1}$ (Assumption T, without its Lipschitz requirement) and
--   $$
--   0\le\gamma\le\frac{m_t}{(Lc_{\max}+P)\,M_{t+1}} .
--   $$
--   Then an optimal policy has the following four-stage structure with thresholds $(s_t,S_t,\sigma_t,\Sigma_t)$:
--
--   1. if $x_t\in[0,\sigma_t)$, then $r^*_t=1$ and $u^*_t=\varphi$;
--   2. if $x_t\in[\sigma_t,s_t)$, then $r^*_t=0$ and $u^*_t=S_t-x_t$;
--   3. if $x_t\in[s_t,\Sigma_t)$, then $r^*_t=0$ and $u^*_t=0$;
--   4. if $x_t\ge\Sigma_t$, then $r^*_t=1$ and $u^*_t=\varphi$,
--
--   where $\varphi\in[0,c_{\max}]$ is a constant.
--
--   Precisely, there is $\varphi\in[0,c_{\max}]$ with $Q_J(0,0,\varphi)=J(0,0)$. For every $t<k$ there are thresholds $0\le\sigma_t\le s_t\le\Sigma_t\le+\infty$ and $S_t\in[0,c_{\max}]$, with $s_t\le S_t$ whenever $\sigma_t<s_t$, such that at every $x\in[0,c_{\max}]$ the action of the policy (23) attains the minimum in (22).
--
--   The reset decision splits the stock axis into a no-reset interval between two reset regions, and inside it the $(s,S)$ rule of Proposition 4 orders.
--
--   Differences from the source:
--   - generalization: AT: J(·,t+1) is piecewise differentiable on a partition of [0, c_max], each piece's derivative bounded by M_{t+1} and Lipschitz continuous → PiecewiseC1: continuous, piecewise C¹ on a partition of [0, c_max] with derivative bounded by M_{t+1}, no Lipschitz requirement on the derivatives; reason: the proofs use only the continuity of the pieces and their derivatives and the bound M_{t+1}; every function satisfying AT satisfies PiecewiseC1
--   - generalization: §2 setting: g ≥ 0 and s ≥ 0 continuous, s(ζ,t,w) ≡ 0 → no sign, continuity or s(ζ,·,·) ≡ 0 condition on H and R beyond A2 and A3; reason: the proofs never use these conditions (continuity of H and R follows from A2 and A3); every instance of the paper satisfies the remaining hypotheses
--   - reading: an optimal policy (for problem (2)) → for every solution J of the dynamic programming equations (22), the policy's action is feasible and its value equals J(x,t), i.e. it attains the minimum in (22); reason: the paper proves optimality with respect to (22) (p.14: 'the optimal fixed point policy π* … to (22)'); the link from (22) to (2) is Proposition 1, cited from Mintz et al. (2017) and not proved in the paper
--   - reading: states x ∈ ℝ₊ (A1), with AT on the domain [0, c_max] → every state, equation and conclusion on x ∈ [0, c_max]; reason: AT and the proofs of Propositions 5 and 6 work on [0, c_max]; from x ≤ c_max the dynamics stay in [0, c_max], and for x > c_max the order set U = [0, c_max − x] of A4 is empty
--   - encoding: thresholds (s_t, S_t, σ_t, Σ_t) defining the four intervals of (23) → ∃ σ_t ≤ s_t ≤ Σ_t in EReal with 0 ≤ σ_t, S_t ∈ [0, c_max], and s_t ≤ S_t when σ_t < s_t; reason: the paper's thresholds may be +∞ (p.33, Figure 6) and its four intervals must partition [0, ∞) for (23) to define a policy; S_t ≥ s_t makes the order S_t − x positive on [σ_t, s_t), as in the paper's construction s_t = s'_t ≤ S'_t
--   - encoding: 0 ≤ γ ≤ m_t/((L c_max + P) M_{t+1}) → 0 ≤ γ and γ · ((L c_max + P) · M_{t+1}) ≤ m_t; reason: equal when M_{t+1} > 0; at M_{t+1} = 0 the paper's quotient is undefined and imposes no bound, while Lean's x/0 = 0 would force γ = 0
--   - encoding: stage cost g(ξ,τ,u,w) and reset cost s(x,t,w), with E g = cu + K·1(u>0) + H(ξ+u,τ) (A2) and R = E s (A3) → the model carries c, K, H and R; reason: g and s enter (22) only through these expectations; same instances
--   - encoding: derivatives ∂ₓH, ∂ₓₓH, ∂ₓR, ∂_zJ_i and the derivatives in the conclusions → derivatives within [0, c_max] (one-sided at 0 and c_max), with the derivative functions named explicitly; reason: at interior points this is the ordinary derivative; at the ends the paper's functions live on [0, c_max], and its retail example (∂ₓₓH = (p+q)f with a jump of f at 0) needs one-sided derivatives
-- source:
--   Lee, Mintz, Aswani, Shen, Yang, Optimal Policy for Inventory Management with Periodic and Controlled Resets, arXiv:2209.03571v1, Proposition 5, p.19; proof, pp.32–35, Figure 6

import Mathlib
import Definitions.Def_ResetInventory_A2
import Definitions.Def_ResetInventory_A3
import Definitions.Def_ResetInventory_A5
import Definitions.Def_ResetInventory_PiecewiseC1
import Definitions.Def_ResetInventory_IsDPSolution
import Definitions.Def_ResetInventory_policy
import Definitions.Def_ResetInventory_IsOptimalAction

namespace ResetInventory

/-- **Proposition 5** of Lee, Mintz, Aswani, Shen, Yang, arXiv:2209.03571v1, p.19. Suppose
`0 ≤ γ ≤ m_t / ((L c_max + P) M_{t+1})` for all `t = 0, …, k − 1`. If A1–A5 and AT hold, then an
optimal policy has the following four-stage structure with `(s_t, S_t, σ_t, Σ_t)` thresholds:

1. if `x_t ∈ [0, σ_t)`, then `r*_t = 1` and `u*_t = ϕ`;
2. if `x_t ∈ [σ_t, s_t)`, then `r*_t = 0` and `u*_t = S_t − x_t`;
3. if `x_t ∈ [s_t, Σ_t)`, then `r*_t = 0` and `u*_t = 0`;
4. if `x_t ≥ Σ_t`, then `r*_t = 1` and `u*_t = ϕ`,

where `ϕ ∈ [0, c_max]` is a constant.

Lean: for every solution `J` of (22), there is `ϕ ∈ [0, c_max]` attaining `J₀ = J(0, 0)`, and for
every `t < k` there are thresholds `0 ≤ σ_t ≤ s_t ≤ Σ_t ≤ +∞` and `S_t ∈ [0, c_max]` with
`s_t ≤ S_t` when `σ_t < s_t`, such that at every `x ∈ [0, c_max]` the action of the policy (23)
attains the minimum in (22).

**Formalization Note** AT at `t` is `PiecewiseC1 c_max M_{t+1} (J(·, t + 1))` (without AT's
Lipschitz requirement). The bound on `γ` is multiplicative, `γ (L c_max + P) M_{t+1} ≤ m_t`.
"Optimal" is attainment of the minimum in (22) (`IsOptimalAction`); the state domain is
`[0, c_max]`; the thresholds are existential, lie in `EReal`, and are ordered, so that the four
intervals of (23) partition `[0, ∞)`. -/
theorem proposition_5_four_stage_policy (mdl : ResetModel) (κ m η Lt : ℕ → ℝ) (L P : ℝ)
    (M : ℕ → ℝ)
    (hcmax : 0 ≤ mdl.cmax) (hc : 0 ≤ mdl.c) (hK : 0 ≤ mdl.K)
    (hγ0 : 0 ≤ mdl.γ) (hγ1 : mdl.γ < 1)
    (hA2 : ∀ t < mdl.k, A2 mdl κ m t) (hA3 : ∀ t < mdl.k, A3 mdl η Lt t)
    (hA5 : A5 mdl.f L P)
    (hγ : ∀ t < mdl.k, mdl.γ * ((L * mdl.cmax + P) * M (t + 1)) ≤ m t)
    (J : ℝ → ℕ → ℝ) (hJ : IsDPSolution mdl J)
    (hAT : ∀ t < mdl.k, PiecewiseC1 mdl.cmax (M (t + 1)) (fun y => J y (t + 1))) :
    ∃ ϕ ∈ Set.Icc 0 mdl.cmax, orderValue mdl J 0 0 ϕ = J 0 0 ∧
      ∀ t < mdl.k, ∃ (σ s Sg : EReal) (S : ℝ),
        0 ≤ σ ∧ σ ≤ s ∧ s ≤ Sg ∧ S ∈ Set.Icc 0 mdl.cmax ∧ (σ < s → s ≤ (S : EReal)) ∧
        ∀ x ∈ Set.Icc 0 mdl.cmax, IsOptimalAction mdl J x t (policy σ s Sg S ϕ x) := by sorry

end ResetInventory
