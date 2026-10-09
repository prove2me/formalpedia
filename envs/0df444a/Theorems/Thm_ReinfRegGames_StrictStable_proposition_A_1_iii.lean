-- Prove2me | Theorems.Thm_ReinfRegGames_StrictStable_proposition_A_1_iii
-- name    : ReinfRegGames.StrictStable.proposition_A_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:05.914874+00:00
-- url     : https://prove2.me/theorems/46a1c325-3dda-4203-882b-7add4cfaf69b
-- title:
--   Proposition A.1(iii), p. 31 — Q_α(y) → 0 whenever y_α − y_β → −∞ for some β ≠ α
-- statement:
--   Let $h$ be a penalty function on the simplex $\Delta=\Delta(B)$ of a finite set $B$ (Definition 2.1, strong convexity constant $K$), and let $Q$ be its choice map, $Q(y)=\arg\max_{x\in\Delta}\{\langle y|x\rangle-h(x)\}$. Let $\alpha\neq\beta$ in $B$. Then $Q_\alpha(y)\to0$ whenever $y_\alpha-y_\beta\to-\infty$; uniformly:
--   $$\forall\varepsilon>0\ \exists M\ \forall y\in\mathbb R^B:\quad y_\alpha-y_\beta<-M\ \Longrightarrow\ Q_\alpha(y)<\varepsilon.$$
--
--   A strategy whose score falls arbitrarily far behind that of another strategy is played with vanishing probability. In the proof of Theorem 5.2 this turns the divergence $z_{k\mu}\to-\infty$ of the relative scores into convergence $x(t)\to x^*$.
--
--   **Formalization Note** The page's "$Q_\alpha(y)\to0$ whenever $y_\alpha-y_\beta\to-\infty$" is stated in the uniform form that the proof (A.3)–(A.4) gives; it is equivalent to the sequential form. $x=Q(y)$ is the predicate "$x$ maximizes $\langle y|\cdot\rangle-h$ over $\Delta$".
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 31, Proposition A.1(iii) (proof (A.3)–(A.4))

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.StrictStable

theorem proposition_A_1_iii {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K)
    (α β : B) (hβα : β ≠ α) :
    ∀ ε > 0, ∃ M : ℝ, ∀ y x : B → ℝ, ReinfRegGames.Extinction.IsChoice h y x → y α - y β < -M → x α < ε := by sorry

end ReinfRegGames.StrictStable
