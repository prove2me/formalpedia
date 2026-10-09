-- Prove2me | Theorems.Thm_RegLearnGames_TotalRegret_lemma_20
-- name    : RegLearnGames.TotalRegret.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:37:01.899421+00:00
-- url     : https://prove2.me/theorems/18dd200b-aa9f-483c-a3e5-fa8e3ce179f8
-- title:
--   Lemma 20, supp. p. 4 — stability of optimistic FTRL: ‖wᵗ−gᵗ‖ ≤ η‖Mᵗ−uᵗ‖_* and ‖gᵗ−wᵗ⁺¹‖ ≤ η‖Mᵗ⁺¹‖_*
-- statement:
--   Let $\Delta \subset \mathbb R^d$ be the probability simplex, $\mathcal R$ a regularizer that is 1-strongly convex with respect to $\|\cdot\|_1$ on $\Delta$, and $\eta > 0$. Let $u^1, u^2, \dots$ and $M^1, M^2, \dots$ be arbitrary utility and predictor sequences in $\mathbb R^d$, let $w^0, w^1, \dots$ be any run of optimistic FTRL and $g^0, g^1, \dots$ any leader sequence for them. Then for every $t \ge 0$,
--   $$\|w^t - g^t\|_1 \le \eta\,\|M^t - u^t\|_\infty \qquad\text{and}\qquad \|g^t - w^{t+1}\|_1 \le \eta\,\|M^{t+1}\|_\infty.$$
--
--   These two stability inequalities say that the iterate is close to the leader when the prediction is accurate, and that one step of the algorithm moves the leader by at most $\eta$ times the size of the next prediction. Combined with Theorem 19 the first gives Proposition 7.
--
--   **Formalization Note** The paper writes the lemma for a general norm $\|\cdot\|$ and its dual; here $\|\cdot\| = \|\cdot\|_1$ and $\|\cdot\|_* = \|\cdot\|_\infty$. At $t = 0$ both $w^0$ and $g^0$ minimize $\mathcal R$ over $\Delta$ (the values $u^0$, $M^0$ play no role in either sequence), so the first inequality holds there as well; it is stated for every $t$.
-- source:
--   Syrgkanis, Agarwal, Luo, Schapire, Fast Convergence of Regularized Learning in Games, arXiv:1507.00407v5, supp. p. 4 (PDF p. 13), App. C, Lemma 20, (14)–(15)

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

namespace RegLearnGames.TotalRegret

theorem lemma_20 {d : ℕ} (𝓡 : (Fin d → ℝ) → ℝ) (η : ℝ) (hη : 0 < η)
    (h𝓡 : IsOneStronglyConvexL1 𝓡)
    (M u w g : ℕ → Fin d → ℝ) (hw : IsOFTRL 𝓡 η M u w) (hg : IsLeader 𝓡 η u g) :
    ∀ t : ℕ, l1 (w t - g t) ≤ η * ‖M t - u t‖ ∧ l1 (g t - w (t + 1)) ≤ η * ‖M (t + 1)‖ := by sorry

end RegLearnGames.TotalRegret
