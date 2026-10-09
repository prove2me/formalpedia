-- Prove2me | Theorems.Thm_ReinfRegGames_TimeAvg_proposition_A_1_iii
-- name    : ReinfRegGames.TimeAvg.proposition_A_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:07:48.686714+00:00
-- url     : https://prove2.me/theorems/a8c9c56d-475e-400c-8c44-d921b5275801
-- title:
--   Proposition A.1(iii), p. 31 — Q_α(y) → 0 whenever y_α − y_β → −∞ for some β ≠ α
-- statement:
--   Let $B$ be a finite set, $h$ a penalty function on $\Delta(B)$ (Definition 2.1) and $Q$ its choice map, $Q(y) = \arg\max_{x\in\Delta}\{\langle y|x\rangle - h(x)\}$. Fix two distinct indices $\alpha \ne \beta$ in $B$. Then the $\alpha$-component of the choice map vanishes when the score of $\alpha$ falls infinitely far behind the score of $\beta$:
--   $$Q_\alpha(y) \to 0 \quad\text{as}\quad y_\alpha - y_\beta \to -\infty,$$
--   in the uniform sense: for every $\varepsilon > 0$ there is $M$ such that $Q_\alpha(y) < \varepsilon$ for every score vector $y$ with $y_\alpha - y_\beta < -M$.
--
--   This is the property that lets a large score gap be read off as a vanishing choice probability; Proposition C.5 uses it.
--
--   **Formalization Note** The page's limit statement ("whenever $y_\alpha - y_\beta \to -\infty$", i.e. along every sequence) is equivalent to the uniform $\varepsilon$–$M$ form stated here. "$x = Q(y)$" is the predicate `IsChoice h y x`, so the bound holds for every maximizer.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 31, Proposition A.1(iii)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.TimeAvg

theorem proposition_A_1_iii {B : Type*} [Fintype B] [DecidableEq B]
    (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K) (α β : B) (hαβ : β ≠ α) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ y x : B → ℝ, ReinfRegGames.Extinction.IsChoice h y x → y α - y β < -M → x α < ε := by sorry

end ReinfRegGames.TimeAvg
