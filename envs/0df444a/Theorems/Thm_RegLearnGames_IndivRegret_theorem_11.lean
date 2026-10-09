-- Prove2me | Theorems.Thm_RegLearnGames_IndivRegret_theorem_11
-- name    : RegLearnGames.IndivRegret.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:32.09097+00:00
-- url     : https://prove2.me/theorems/6c8e3d3c-1963-405e-ae1d-5a30068a62d2
-- title:
--   Theorem 11, p. 5 — RVU (α > 0, β > 0, γ ≥ 0) and stability κ give each player regret ≤ α + βκ²(n−1)²T
-- statement:
--   Consider an $n$-player game in which every player has $d$ strategies and utilities $u_i(s)\in[0,1]$, played repeatedly: $w^0,w^1,w^2,\dots$ are mixed profiles, and $u_i^t$ is player $i$'s utility vector against $w^t$. Let $\alpha>0$, $\beta>0$, $\gamma\ge0$ and fix a horizon $T$. Suppose that every player's play satisfies the RVU inequality: for every player $i$ and every $v\in\Delta$,
--   $$\sum_{t=1}^T\langle v-w_i^t,u_i^t\rangle\le\alpha+\beta\sum_{t=1}^T\|u_i^t-u_i^{t-1}\|_\infty^2-\gamma\sum_{t=1}^T\|w_i^t-w_i^{t-1}\|_1^2 ,$$
--   and that the play is stable: $\|w_i^t-w_i^{t+1}\|_1\le\kappa$ for every player $i$ and every $t=0,\dots,T-1$. Then for every player $i$ and every $w_i^*\in\Delta$,
--   $$\sum_{t=1}^T\langle w_i^*-w_i^t,u_i^t\rangle\le\alpha+\beta\kappa^2(n-1)^2T .$$
--
--   In words, if the players use algorithms with the RVU property that also move slowly, then each player's regret grows like $\beta\kappa^2(n-1)^2T$; for optimistic FTRL, $\beta=\eta$ and $\kappa=2\eta$, so the growth is of order $\eta^3$, which is what the choice of step size in Corollary 12 exploits.
--
--   **Formalization Note** The paper assumes the RVU property on any utility sequence; here it is assumed only on the realized play, which is weaker as a hypothesis and makes the theorem stronger. The paper's parameters "$\alpha>0,\beta>0,\gamma\ge0$" are kept and Definition 3's $\beta\le\gamma$ is not required, since the proof does not use it. Stability is required for the movements $t=0,\dots,T-1$ that enter the sum. The vector $u_i^0$ is the utility vector against $w^0$.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 5, §3.2, Theorem 11

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.IndivRegret

theorem theorem_11 {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w : ℕ → Fin n → Fin d → ℝ) (hw : ∀ t i, w t i ∈ stdSimplex ℝ (Fin d))
    (α β γ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) (T : ℕ)
    (hRVU : ∀ i, ∀ v ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (v - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i ≤
        α + β * ∑ t ∈ Finset.Icc 1 T, ‖RegLearnGames.TotalRegret.utilVec u (w t) i - RegLearnGames.TotalRegret.utilVec u (w (t - 1)) i‖ ^ 2
          - γ * ∑ t ∈ Finset.Icc 1 T, RegLearnGames.TotalRegret.l1 (w t i - w (t - 1) i) ^ 2)
    (κ : ℝ) (hκ : ∀ i, ∀ t < T, RegLearnGames.TotalRegret.l1 (w t i - w (t + 1) i) ≤ κ) :
    ∀ i, ∀ wstar ∈ stdSimplex ℝ (Fin d),
      ∑ t ∈ Finset.Icc 1 T, (wstar - w t i) ⬝ᵥ RegLearnGames.TotalRegret.utilVec u (w t) i ≤
        α + β * κ ^ 2 * ((n : ℝ) - 1) ^ 2 * T := by sorry

end RegLearnGames.IndivRegret
