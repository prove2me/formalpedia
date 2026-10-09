-- Prove2me | Theorems.Thm_RegLearnGames_TotalRegret_proposition_7
-- name    : RegLearnGames.TotalRegret.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:21.856986+00:00
-- url     : https://prove2.me/theorems/d439320e-29b4-4ff3-8255-297d2bcbf7c9
-- title:
--   Proposition 7, p. 5 — OFTRL with Mᵗ = uᵗ⁻¹ has the RVU property with α = R/η, β = η, γ = 1/(4η)
-- statement:
--   Let $\Delta \subset \mathbb R^d$ be the probability simplex, $\mathcal R$ a regularizer that is 1-strongly convex with respect to $\|\cdot\|_1$ on $\Delta$, $\eta > 0$, and $R$ a bound on the range of $\mathcal R$ on $\Delta$. Let $u^0, u^1, u^2, \dots$ be an arbitrary utility sequence in $\mathbb R^d$, and let $w^0, w^1, \dots$ be any run of optimistic FTRL with the one-step recency bias $M^t = u^{t-1}$. Then for every horizon $T$ and every comparator $w^* \in \Delta$,
--   $$\sum_{t=1}^T \langle w^* - w^t, u^t\rangle \le \frac{R}{\eta} + \eta\sum_{t=1}^T \|u^t - u^{t-1}\|_\infty^2 - \frac{1}{4\eta}\sum_{t=1}^T \|w^t - w^{t-1}\|_1^2.$$
--
--   This is inequality (1) of Definition 3 — regret bounded by variation in utilities (RVU) — with constants $\alpha = R/\eta$, $\beta = \eta$ and $\gamma = 1/(4\eta)$. Together with Theorem 4 it gives Corollary 8.
--
--   **Formalization Note** "Satisfies the RVU property" is rendered as inequality (1) for every utility sequence, every horizon and every comparator. Definition 3 also asks $\alpha > 0$ and $0 < \beta \le \gamma$ of the constants; these hold when $R > 0$ and $\eta \le 1/2$ and are not part of the conclusion. The norm is $\ell_1$ with dual $\ell_\infty$ (the paper allows any norm). $R$ is any upper bound on the range of $\mathcal R$ over $\Delta$, which includes the paper's $\sup - \inf$.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 5, Proposition 7 (R as defined just above it); Definition 3, inequality (1), p. 3; proof supp. pp. 2–5 (PDF pp. 11–14)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.TotalRegret

theorem proposition_7 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η R : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (u w : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η (fun T => u (T - 1)) u w)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + η * ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ ^ 2
        - 1 / (4 * η) * ∑ t ∈ Finset.Icc 1 T, l1 (w t - w (t - 1)) ^ 2 := by sorry

end RegLearnGames.TotalRegret
