-- Prove2me | Theorems.Thm_RegLearnGames_IndivRegret_proposition_7
-- name    : RegLearnGames.IndivRegret.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:18.771986+00:00
-- url     : https://prove2.me/theorems/344fc5d4-2562-4f4c-bf2c-f139ff2fda44
-- title:
--   Proposition 7, p. 5 — OFTRL with Mᵗ = uᵗ⁻¹ satisfies RVU with α = R/η, β = η, γ = 1/(4η)
-- statement:
--   Let $\mathcal R$ be a regularizer on $\mathbb R^d$ that is 1-strongly convex with respect to $\|\cdot\|_1$ on the simplex $\Delta$, let $\eta>0$, and let $R$ bound the range of $\mathcal R$ on $\Delta$: $\mathcal R(f)-\mathcal R(g)\le R$ for all $f,g\in\Delta$. Let $u^0,u^1,\dots$ be any utility sequence in $\mathbb R^d$ and let $w^0,w^1,\dots$ be a run of optimistic FTRL with regularizer $\mathcal R$, step size $\eta$ and one-step recency bias $M^t=u^{t-1}$. Then for every horizon $T$ and every comparator $w^*\in\Delta$,
--   $$\sum_{t=1}^T\langle w^*-w^t,u^t\rangle\le\frac R\eta+\eta\sum_{t=1}^T\|u^t-u^{t-1}\|_\infty^2-\frac1{4\eta}\sum_{t=1}^T\|w^t-w^{t-1}\|_1^2 .$$
--
--   This is the RVU property (Regret bounded by Variation in Utilities, Definition 3 of the paper) with constants $\alpha=R/\eta$, $\beta=\eta$, $\gamma=1/(4\eta)$. The negative movement term is what lets the regret of interacting players stay small.
--
--   **Formalization Note** "Satisfies the RVU property" is formalized as inequality (1) holding on every utility sequence, which is what the quantification over $u$ gives; the side conditions $\alpha>0$, $0<\beta\le\gamma$ of Definition 3 are conditions on the constants and are not part of the conclusion. The paper's $R=\sup_\Delta\mathcal R-\inf_\Delta\mathcal R$ is replaced by any upper bound on that range, which includes the exact range. The norm is $\|\cdot\|_1$ with dual $\|\cdot\|_\infty$. This statement coincides with the one of the companion mission I of this series.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, p. 5, Proposition 7 (R defined just above it); proof supp. pp. 2–5 (PDF pp. 11–14)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.IndivRegret

theorem proposition_7 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : RegLearnGames.TotalRegret.IsOneStronglyConvexL1 𝓡) (R : ℝ)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (u w : ℕ → Fin d → ℝ) (hw : RegLearnGames.TotalRegret.IsOFTRL 𝓡 η (fun T => u (T - 1)) u w)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + η * ∑ t ∈ Finset.Icc 1 T, ‖u t - u (t - 1)‖ ^ 2
        - (1 / (4 * η)) * ∑ t ∈ Finset.Icc 1 T, RegLearnGames.TotalRegret.l1 (w t - w (t - 1)) ^ 2 := by sorry

end RegLearnGames.IndivRegret
