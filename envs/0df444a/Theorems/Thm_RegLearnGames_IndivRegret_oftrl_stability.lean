-- Prove2me | Theorems.Thm_RegLearnGames_IndivRegret_oftrl_stability
-- name    : RegLearnGames.IndivRegret.oftrl_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:36.159369+00:00
-- url     : https://prove2.me/theorems/e451c7f8-8563-4828-92f4-930ddb2f4419
-- title:
--   p. 5, the claim before Corollary 12 — optimistic FTRL with Mᵗ = uᵗ⁻¹ and utilities in [0,1] is stable with κ = 2η
-- statement:
--   Let $\mathcal R$ be a regularizer on $\mathbb R^d$ that is 1-strongly convex with respect to $\|\cdot\|_1$ on the simplex $\Delta$, and let $\eta>0$. Let $u^0,u^1,\dots$ be a utility sequence with every entry in $[0,1]$, and let $w^0,w^1,\dots$ be a run of optimistic FTRL with regularizer $\mathcal R$, step size $\eta$ and one-step recency bias $M^t=u^{t-1}$. Then for every $t\ge0$,
--   $$\|w^t-w^{t+1}\|_1\le 2\eta .$$
--
--   This is the *stability property* with $\kappa=2\eta$ that the paper invokes, citing Lemma 20, to apply Theorem 11 to optimistic FTRL; it is the step that turns the regret bound of Theorem 11 into the $T^{1/4}$ rate of Corollary 12.
--
--   **Formalization Note** The bound $u^t_x\in[0,1]$ is the paper's standing assumption $u_i : S\to[0,1]$ (§2), which makes every utility vector lie in $[0,1]^d$; it is what bounds $\|M^t-u^t\|_\infty$ and $\|M^{t+1}\|_\infty$ by $1$. At $T=1$ the predictor is $M^1=u^0$, so the bound at $t=0$ is about the first move from $w^0=\operatorname{argmin}_\Delta\mathcal R$. The norm is $\|\cdot\|_1$.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 5, §3.2, the sentence before Corollary 12 ("stability property with κ = 2η (see Lemma 20 in the appendix)")

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.IndivRegret

theorem oftrl_stability {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : RegLearnGames.TotalRegret.IsOneStronglyConvexL1 𝓡) (u w : ℕ → Fin d → ℝ)
    (hu : ∀ t x, u t x ∈ Set.Icc (0 : ℝ) 1)
    (hw : RegLearnGames.TotalRegret.IsOFTRL 𝓡 η (fun T => u (T - 1)) u w) :
    ∀ t, RegLearnGames.TotalRegret.l1 (w t - w (t + 1)) ≤ 2 * η := by sorry

end RegLearnGames.IndivRegret
