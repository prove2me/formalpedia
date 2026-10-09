-- Prove2me | Theorems.Thm_RegLearnGames_IndivRegret_corollary_12
-- name    : RegLearnGames.IndivRegret.corollary_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:36.269627+00:00
-- url     : https://prove2.me/theorems/c636c263-d121-413d-bf11-1d23ebba7448
-- title:
--   Corollary 12, p. 5 — OFTRL with η = (n−1)^{−1/2}T^{−1/4} for every player: each regret ≤ (R+4)√(n−1)·T^{1/4}
-- statement:
--   Consider an $n$-player game with $n\ge2$ in which every player has $d$ strategies and utilities $u_i(s)\in[0,1]$. Each player $i$ has a regularizer $\mathcal R_i$ that is 1-strongly convex with respect to $\|\cdot\|_1$ on the simplex $\Delta$, and $R$ bounds every range: $\mathcal R_i(f)-\mathcal R_i(g)\le R$ for all $i$ and all $f,g\in\Delta$. Fix a horizon $T\ge1$ and the step size
--   $$\eta=(n-1)^{-1/2}\,T^{-1/4}.$$
--   Suppose the game is played repeatedly and every player runs optimistic FTRL with regularizer $\mathcal R_i$, step size $\eta$ and one-step recency bias $M_i^t=u_i^{t-1}$, where $u_i^t$ is player $i$'s utility vector against the profile $w^t$ played at time $t$. Then for every player $i$ and every fixed strategy $w_i^*\in\Delta$,
--   $$\sum_{t=1}^T\langle w_i^*-w_i^t,u_i^t\rangle\le(R+4)\sqrt{n-1}\cdot T^{1/4}.$$
--
--   Each player's regret thus grows like $T^{1/4}$, so its average regret decays like $T^{-3/4}$, against the $T^{-1/2}$ rate that holds against an adversary. It is the paper's result on the convergence of individual utilities.
--
--   **Formalization Note** The conditions $n\ge2$ and $T\ge1$ are added because the step size is undefined otherwise. The paper's $R=\max_i(\sup_\Delta\mathcal R_i-\inf_\Delta\mathcal R_i)$ is replaced by any common upper bound on the ranges, which includes the exact value. The regret $r_i(T)=\sup_{w^*}\sum_t\langle w^*-w_i^t,u_i^t\rangle$ is bounded through every comparator $w^*\in\Delta$. The statement covers every run of the dynamics, and the vector $u_i^0$ entering $M_i^1$ is the utility vector against $w^0$. The horizon $T$ is fixed before play, because $\eta$ depends on it.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 5, §3.2, Corollary 12

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.IndivRegret

theorem corollary_12 {n d : ℕ} (hn : 2 ≤ n) (T : ℕ) (hT : 1 ≤ T)
    (u : Fin n → (Fin n → Fin d) → ℝ) (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ) (h𝓡 : ∀ i, RegLearnGames.TotalRegret.IsOneStronglyConvexL1 (𝓡 i)) (R : ℝ)
    (hR : ∀ i, ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 i f - 𝓡 i g ≤ R)
    (w : ℕ → Fin n → Fin d → ℝ)
    (hw : RegLearnGames.TotalRegret.IsOFTRLDynamics u 𝓡
      (((n : ℝ) - 1) ^ (-(1 : ℝ) / 2) * (T : ℝ) ^ (-(1 : ℝ) / 4)) w) :
    ∀ i, ∀ wstar ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (wstar - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i ≤
        (R + 4) * Real.sqrt ((n : ℝ) - 1) * (T : ℝ) ^ ((1 : ℝ) / 4) := by sorry

end RegLearnGames.IndivRegret
