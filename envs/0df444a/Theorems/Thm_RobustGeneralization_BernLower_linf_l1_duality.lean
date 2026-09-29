-- Prove2me | Theorems.Thm_RobustGeneralization_BernLower_linf_l1_duality
-- name    : RobustGeneralization.BernLower.linf_l1_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:21:41.479987+00:00
-- url     : https://prove2.me/theorems/40610578-42ce-42b3-a64f-550c7220b9ad
-- title:
--   §4 (p. 10) — sup over ‖Δ‖∞ ≤ ε of ⟨yw, Δ⟩ is ε‖w‖₁; robust margin iff ⟨yw, x⟩ > ε‖w‖₁
-- statement:
--   Let $w,x\in\mathbb R^d$, $y\in\{\pm1\}$ and $\varepsilon\ge0$. Then the supremum of $\langle yw,\Delta\rangle$ over perturbations with $\|\Delta\|_\infty\le\varepsilon$ is attained and equals $\varepsilon\|w\|_1$:
--   $$\max_{\Delta:\|\Delta\|_\infty\le\varepsilon}\langle yw,\Delta\rangle=\varepsilon\|yw\|_1=\varepsilon\|w\|_1,$$
--   and the linear classifier $w$ classifies $x$ with positive margin on the whole ball, i.e. $\langle yw,x'\rangle>0$ for every $x'$ with $\|x'-x\|_\infty\le\varepsilon$, if and only if
--   $$\langle yw,x\rangle>\varepsilon\|w\|_1.$$
--
--   This is the observation that ties $\ell_\infty$-robustness of a linear classifier to the $\ell_1$ norm of its weight vector, the starting point of the lower bound for linear classifiers.
--
--   **Formalization Note** $\|\Delta\|_\infty\le\varepsilon$ and $\|w\|_1$ are written coordinatewise ($|\Delta_i|\le\varepsilon$ for all $i$, $\sum_i|w_i|$). The criterion is the margin condition $\inf_{\Delta}\langle yw,x+\Delta\rangle>0$ of the page, which is stated as "for all points of the ball" since the infimum over the compact ball is attained. $\varepsilon\ge0$ is needed for the ball to be nonempty.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 10, §4, the displays from 'For an example (x, y), a linear classifier' to 'ε‖yw‖₁ = ε‖w‖₁'

import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem linf_l1_duality (d : ℕ) (w x : E d) (y : Bool) (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest {t : ℝ | ∃ Δ : E d, (∀ i, |Δ i| ≤ ε) ∧ t = inner ℝ (lab y • w) Δ}
        (ε * ∑ i, |w i|) ∧
      ((∀ x' ∈ linfBall x ε, 0 < inner ℝ (lab y • w) x') ↔
        ε * ∑ i, |w i| < inner ℝ (lab y • w) x) := by sorry

end RobustGeneralization.BernLower
