-- Prove2me | Theorems.Thm_RegLearnGames_IndivRegret_lemma_20
-- name    : RegLearnGames.IndivRegret.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:02.525299+00:00
-- url     : https://prove2.me/theorems/7dcb1416-00c4-4740-9467-6a940ec37edb
-- title:
--   Lemma 20, supp. p. 4 — stability of optimistic FTRL: ‖wᵗ−gᵗ‖ ≤ η‖Mᵗ−uᵗ‖_*, ‖gᵗ−wᵗ⁺¹‖ ≤ η‖Mᵗ⁺¹‖_*
-- statement:
--   Let $\mathcal R$ be a regularizer on $\mathbb R^d$ that is 1-strongly convex with respect to $\|\cdot\|_1$ on the simplex $\Delta$, and let $\eta>0$. Let $u^1,u^2,\dots$ be any utility sequence and $M^1,M^2,\dots$ any predictor sequence in $\mathbb R^d$. Let $w^0,w^1,\dots$ be a run of optimistic FTRL with regularizer $\mathcal R$, step size $\eta$ and predictors $M^t$, and let $g^0,g^1,\dots$ be the corresponding leader sequence. Then for every $t$,
--   $$\|w^t-g^t\|_1\le\eta\,\|M^t-u^t\|_\infty\qquad\text{and}\qquad\|g^t-w^{t+1}\|_1\le\eta\,\|M^{t+1}\|_\infty .$$
--
--   The first bound says the optimistic iterate is close to the leader when the prediction $M^t$ is close to the realized utility $u^t$; the second says consecutive iterates move by at most $\eta$ times the size of the next prediction. Together they give the stability of optimistic FTRL used in Proposition 7 and in Corollary 12.
--
--   **Formalization Note** The paper states the lemma for a general norm; it is formalized for $\|\cdot\|_1$ and its dual $\|\cdot\|_\infty$, the case the mission's goal uses. The values $u^0$ and $M^0$ are arbitrary (they enter only the bound at $t=0$, where $w^0$ and $g^0$ both minimize $\mathcal R$). This statement coincides with the one of the companion mission I of this series.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 4 (PDF p. 13), Lemma 20, (14)–(15)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.IndivRegret

theorem lemma_20 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : RegLearnGames.TotalRegret.IsOneStronglyConvexL1 𝓡) (M u w g : ℕ → Fin d → ℝ)
    (hw : RegLearnGames.TotalRegret.IsOFTRL 𝓡 η M u w) (hg : RegLearnGames.TotalRegret.IsLeader 𝓡 η u g) :
    ∀ t, RegLearnGames.TotalRegret.l1 (w t - g t) ≤ η * ‖M t - u t‖ ∧ RegLearnGames.TotalRegret.l1 (g t - w (t + 1)) ≤ η * ‖M (t + 1)‖ := by sorry

end RegLearnGames.IndivRegret
