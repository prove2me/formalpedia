-- Prove2me | Theorems.Thm_RegLearnGames_TotalRegret_theorem_19
-- name    : RegLearnGames.TotalRegret.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:05.813185+00:00
-- url     : https://prove2.me/theorems/e0168ad5-3ef3-4991-ab9e-4a94abdc7091
-- title:
--   Theorem 19, supp. p. 3 — optimistic FTRL regret ≤ R/η + Σ‖uᵗ−Mᵗ‖_*‖wᵗ−gᵗ‖ − (1/2η)Σ(‖wᵗ−gᵗ‖² + ‖wᵗ−gᵗ⁻¹‖²)
-- statement:
--   Let $\Delta \subset \mathbb R^d$ be the probability simplex, $\mathcal R$ a regularizer that is 1-strongly convex with respect to $\|\cdot\|_1$ on $\Delta$, $\eta > 0$ a step size, and $R$ a bound on the range of $\mathcal R$ on $\Delta$: $\mathcal R(f) - \mathcal R(g) \le R$ for all $f, g \in \Delta$. Let $u^1, u^2, \dots$ be an arbitrary utility sequence and $M^1, M^2, \dots$ an arbitrary predictor sequence in $\mathbb R^d$, let $w^0, w^1, \dots$ be any run of optimistic FTRL on them, and let $g^0, g^1, \dots$ be any leader sequence, $g^T \in \operatorname{argmax}_{g\in\Delta}\langle g, \sum_{t=1}^T u^t\rangle - \mathcal R(g)/\eta$. Then for every horizon $T$ and every comparator $w^* \in \Delta$,
--   $$\sum_{t=1}^T \langle w^* - w^t, u^t\rangle \le \frac{R}{\eta} + \sum_{t=1}^T \|u^t - M^t\|_*\,\|w^t - g^t\| - \frac{1}{2\eta}\sum_{t=1}^T \big(\|w^t - g^t\|^2 + \|w^t - g^{t-1}\|^2\big),$$
--   where $\|\cdot\| = \|\cdot\|_1$ and $\|\cdot\|_* = \|\cdot\|_\infty$.
--
--   This is the basic regret bound of optimistic FTRL. Its negative terms, which measure how far each iterate is from the leader, are what Proposition 7 converts into the negative movement term of the RVU property.
--
--   **Formalization Note** The paper states the result for a single player and a general norm with $R = \sup_f \mathcal R(f) - \inf_f \mathcal R(f)$; here the norm is $\ell_1$ (the case Theorem 4 and Corollary 8 use), and $R$ is any upper bound on the range of $\mathcal R$ over $\Delta$, which includes the exact range. The utilities and predictors are arbitrary real vectors, as on the page.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 3 (PDF p. 12), App. C, Theorem 19, inequality (11)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.TotalRegret

theorem theorem_19 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η R : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (hR : ∀ f ∈ stdSimplex ℝ (Fin d), ∀ g ∈ stdSimplex ℝ (Fin d), 𝓡 f - 𝓡 g ≤ R)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g)
    (T : ℕ) (wstar : Fin d → ℝ) (hwstar : wstar ∈ stdSimplex ℝ (Fin d)) :
    ∑ t ∈ Finset.Icc 1 T, (wstar - w t) ⬝ᵥ u t ≤
      R / η + ∑ t ∈ Finset.Icc 1 T, ‖u t - M t‖ * l1 (w t - g t)
        - 1 / (2 * η) * ∑ t ∈ Finset.Icc 1 T, (l1 (w t - g t) ^ 2 + l1 (w t - g (t - 1)) ^ 2) := by sorry

end RegLearnGames.TotalRegret
