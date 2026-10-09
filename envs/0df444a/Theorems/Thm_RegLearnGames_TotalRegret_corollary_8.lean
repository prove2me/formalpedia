-- Prove2me | Theorems.Thm_RegLearnGames_TotalRegret_corollary_8
-- name    : RegLearnGames.TotalRegret.corollary_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:04.426388+00:00
-- url     : https://prove2.me/theorems/a9a7b4f7-6a39-4aae-b713-26a3b1f87ca8
-- title:
--   Corollary 8, p. 5 — optimistic FTRL with η = 1/(2(n−1)) for every player: Σᵢ rᵢ(T) ≤ nR/η = 2n(n−1)R
-- statement:
--   Consider an $n$-player game, $n \ge 2$, with $d$ strategies per player and utilities $u_i(s) \in [0,1]$. Each player $i$ has a regularizer $\mathcal R_i$ that is 1-strongly convex with respect to $\|\cdot\|_1$ on the simplex $\Delta$, and $R$ bounds the range of every regularizer on $\Delta$: $\mathcal R_i(f) - \mathcal R_i(g) \le R$ for all $i$ and $f, g \in \Delta$ (so $R$ may be taken to be $\max_i(\sup_\Delta \mathcal R_i - \inf_\Delta \mathcal R_i)$). Suppose every player runs optimistic FTRL with step size
--   $$\eta = \frac{1}{2(n-1)}$$
--   and one-step recency bias $M_i^t = u_i^{t-1}$, where $u_i^t$ is player $i$'s utility vector against the others' mixed strategies at time $t$ (with $u_i^0$ computed from the initial profile $w^0$). Then for every horizon $T$ and every profile of comparators $(w_i^*)_i$ with each $w_i^* \in \Delta$,
--   $$\sum_{i} \sum_{t=1}^T \langle w_i^* - w_i^t, u_i^t\rangle \le \frac{nR}{\eta} = 2n(n-1)R,$$
--   that is, $\sum_{i} r_i(T) \le nR/\eta = 2n(n-1)R$, a bound independent of $T$.
--
--   This is the paper's constant bound on the total regret of uncoupled no-regret dynamics in general games; with Proposition 2 it gives convergence of the average welfare at rate $O(1/T)$.
--
--   **Formalization Note** The statement holds for every joint trajectory produced by the dynamics (OFTRL is an argmax predicate). $2 \le n$ is added because $\eta$ is undefined at $n = 1$. Per-player regularizers are allowed (footnote 2), a generalization of a common $\mathcal R$. Continuity of each $\mathcal R_i$ on $\Delta$ is part of strong convexity here (see the Setting). The "$= O(1)$" of the page is not stated; the identity $nR/\eta = 2n(n-1)R$ is the second conjunct.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 5, Corollary 8 (R as defined before Proposition 7)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.TotalRegret

theorem corollary_8 {n d : ℕ} (hn : 2 ≤ n) (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (𝓡 : Fin n → (Fin d → ℝ) → ℝ) (h𝓡 : ∀ i, IsOneStronglyConvexL1 (𝓡 i))
    (R : ℝ) (hR : ∀ i, ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 i f - 𝓡 i g ≤ R)
    (w : ℕ → Fin n → Fin d → ℝ) (hw : IsOFTRLDynamics u 𝓡 (1 / (2 * ((n : ℝ) - 1))) w)
    (T : ℕ) (wstar : Fin n → Fin d → ℝ) (hwstar : ∀ i, wstar i ∈ stdSimplex ℝ (Fin d)) :
    ∑ i, ∑ t ∈ Finset.Icc 1 T, (wstar i - w t i) ⬝ᵥ utilVec u (w t) i ≤
        n * R / (1 / (2 * ((n : ℝ) - 1))) ∧
      n * R / (1 / (2 * ((n : ℝ) - 1))) = 2 * n * ((n : ℝ) - 1) * R := by sorry

end RegLearnGames.TotalRegret
