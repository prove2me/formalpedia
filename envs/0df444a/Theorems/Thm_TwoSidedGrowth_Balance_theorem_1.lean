-- Prove2me | Theorems.Thm_TwoSidedGrowth_Balance_theorem_1
-- name    : TwoSidedGrowth.Balance.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:21.879141+00:00
-- url     : https://prove2.me/theorems/292fa610-c6ca-460a-b696-67e08c2d8fa3
-- title:
--   Theorem 1, p. 19 — the optimal market balance is the clamped inverse (14) and moves monotonically between the output- and durability-maximizing balances
-- statement:
--   **Theorem 1 (Optimal Balance).** Consider the two-sided growth model in size-balance form under its standing assumptions: output $g(\gamma,x)=x^{\alpha}h(\gamma)$, net welfare rate $G(\gamma,x)=(v-c)g(\gamma,x)-(\rho+\beta^s_0\gamma+\beta^d_0(1-\gamma))x$, and Assumptions 1–4 on $h$. Write $\kappa(x)=(\beta^s_0-\beta^d_0)x^{1-\alpha}/(v-c)$. Then:
--
--   1. for every market size $x>0$ exactly one balance satisfies
--   $$\gamma^*(x)=\max\Bigl\{\min\Bigl\{(h')^{-1}\Bigl(\frac{(\beta^s_0-\beta^d_0)x^{1-\alpha}}{v-c}\Bigr),1\Bigr\},0\Bigr\};\tag{14}$$
--   2. a balance $\gamma\in[0,1]$ maximizes $G(\cdot,x)$ over $[0,1]$ if and only if it satisfies (14);
--   3. along any size path, the balance path $\gamma^*(x(t))$ is optimal in (13): for every horizon $T\ge 0$ and any two admissible triples $(x,\gamma,\pi)$ and $(x,\gamma_b,\pi_b)$ with the same size path $x$ and $\gamma_b(t)$ satisfying (14) at $x(t)$ for all $t\in[0,T]$,
--   $$\int_0^T e^{-\rho t}\pi\,g(\gamma,x)\,dt\ \le\ \int_0^T e^{-\rho t}\pi_b\,g(\gamma_b,x)\,dt;$$
--   4. let $\gamma^*(x)$ denote the balance of (14) at each $x>0$ and let $\gamma_o\in(0,1)$ be the output-maximizing balance, $h'(\gamma_o)=0$. As $x$ grows from $0$ to $\infty$:
--       - decreasing returns ($\alpha<1$) and more durable demand ($\beta^s_0>\beta^d_0$): $\gamma^*$ is decreasing, from $\gamma_o$ to $0$;
--       - decreasing returns and more durable supply ($\beta^s_0<\beta^d_0$): $\gamma^*$ is increasing, from $\gamma_o$ to $1$;
--       - increasing returns ($\alpha>1$) and more durable demand: $\gamma^*$ is increasing, from $0$ to $\gamma_o$;
--       - increasing returns and more durable supply: $\gamma^*$ is decreasing, from $1$ to $\gamma_o$.
--
--   The optimal balance thus depends only on the current market size, and it trades off durability (concentrating the market on the side that attrites less) against output (the balance that maximizes $h$), with the side favoured at small and at large sizes determined by the returns to scale.
--
--   **Formalization Note.** "Decreasing (increasing)" is monotone on $(0,\infty)$ and strictly monotone on the set of sizes where $\gamma^*(x)\in(0,1)$; when $h'$ is bounded at an end, $\gamma^*$ is constant at $0$ or $1$ on a whole tail, so strict monotonicity everywhere would be false. "From $a$ to $b$" means the limits as $x\to 0^+$ and $x\to\infty$. The output-maximizing balance (also written $\gamma^*$ in the paper) is any zero of $h'$ in $(0,1)$, unique by Assumption 3. Optimality in (13) is posed on every finite horizon, for smooth paths with the same size trajectory (§3.5 poses the problem "in the space of the market size trajectory"); impulse controls are not modelled. The case $\alpha=1$ is not covered, as in the paper.
-- source:
--   Lian, van Ryzin, Optimal Growth in Two-Sided Markets, SSRN working paper 3310559 (version of 2020-01-16), p. 19, Theorem 1

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Setting

open Filter Topology

namespace TwoSidedGrowth.Balance
theorem theorem_1 (M : Model) (hM : M.Standing) :
    (∀ x : ℝ, 0 < x → ∃! γ : ℝ, IsBalance M x γ) ∧
    (∀ x : ℝ, 0 < x → ∀ γ ∈ Set.Icc (0:ℝ) 1,
      ((∀ η ∈ Set.Icc (0:ℝ) 1, G M η x ≤ G M γ x) ↔ IsBalance M x γ)) ∧
    (∀ (T : ℝ) (x γ pm γb pmb : ℝ → ℝ), Admissible M T x γ pm → Admissible M T x γb pmb →
      (∀ t ∈ Set.Icc 0 T, IsBalance M (x t) (γb t)) →
      profit M T x γ pm ≤ profit M T x γb pmb) ∧
    (∀ γs : ℝ → ℝ, (∀ x : ℝ, 0 < x → IsBalance M x (γs x)) →
      ∀ γo ∈ Set.Ioo (0:ℝ) 1, deriv (h M) γo = 0 →
      (M.α < 1 → M.bd0 < M.bs0 →
        AntitoneOn γs (Set.Ioi 0) ∧ StrictAntiOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 γo) ∧ Tendsto γs atTop (𝓝 0)) ∧
      (M.α < 1 → M.bs0 < M.bd0 →
        MonotoneOn γs (Set.Ioi 0) ∧ StrictMonoOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 γo) ∧ Tendsto γs atTop (𝓝 1)) ∧
      (1 < M.α → M.bd0 < M.bs0 →
        MonotoneOn γs (Set.Ioi 0) ∧ StrictMonoOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 0) ∧ Tendsto γs atTop (𝓝 γo)) ∧
      (1 < M.α → M.bs0 < M.bd0 →
        AntitoneOn γs (Set.Ioi 0) ∧ StrictAntiOn γs {x | 0 < x ∧ γs x ∈ Set.Ioo 0 1} ∧
        Tendsto γs (𝓝[>] 0) (𝓝 1) ∧ Tendsto γs atTop (𝓝 γo))) := by sorry
end TwoSidedGrowth.Balance
