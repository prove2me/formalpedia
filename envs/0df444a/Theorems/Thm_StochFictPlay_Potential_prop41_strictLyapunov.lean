-- Prove2me | Theorems.Thm_StochFictPlay_Potential_prop41_strictLyapunov
-- name    : StochFictPlay.Potential.prop41_strictLyapunov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:10:36.616469+00:00
-- url     : https://prove2.me/theorems/12109617-dec9-4c29-be8d-d2f8b42f526d
-- title:
--   Proposition 4.1 — in a potential game $\Pi$ is a strict Lyapunov function for (PV)
-- statement:
--   Let $G$ be a $p$ player potential game ($p \ge 2$, every strategy set nonempty), so all players have the same utility $u^1 = \dots = u^p$. For each player $\alpha$ let $V^\alpha$ be an admissible deterministic perturbation and let $\tilde C^\alpha(\pi)$ be the unique maximizer of $y\cdot\pi - V^\alpha(y)$ over $\operatorname{int}(\Delta S^\alpha)$. Then
--   $$\Pi(x^1,\dots,x^p) = \sum_{s\in S}\Big(u^1(s)\prod_\alpha x^\alpha_{s^\alpha}\Big) - \sum_\alpha V^\alpha(x^\alpha)$$
--   is a strict Lyapunov function for the dynamic
--   $$(PV)\qquad \dot x^\alpha = \tilde C^\alpha\big(U^\alpha(x^{-\alpha})\big) - x^\alpha$$
--   on $\Sigma$: along every solution in $\Sigma$ that is not constant, $\Pi$ is strictly increasing on $(0,\infty)$.
--
--   This is the Lyapunov function behind all of §4.2: its critical points are the rest points of (PV), and its critical values control the chain recurrent set.
--
--   **Formalization Note** Player 1 is index $0$. The paper's (PV) ends in "$-x$", a slip for "$-x^\alpha$". Strict increase is required for $t > 0$, since $V^\alpha$ is only meaningful on the interior of the simplex and a solution from a boundary point is interior at every $t > 0$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 17, Proposition 4.1 (proof p. 27)

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel
import Definitions.Def_StochFictPlay_Potential_Dynamics
import Definitions.Def_StochFictPlay_Potential_Game
import Definitions.Def_StochFictPlay_Potential_PotentialGame

namespace StochFictPlay.Potential

/-- Proposition 4.1 (Hofbauer–Sandholm 2002, manuscript p. 17). In a `p` player potential game
(identical payoffs `u^α = u^β`), let each `V^α` be an admissible deterministic perturbation and
`Ct α π` the unique maximizer of `y ↦ y · π − V^α(y)` over `int(∆S^α)`. Then
`Π(x) = ∑_{s ∈ S} u¹(s) ∏_α x^α_{s^α} − ∑_α V^α(x^α)` is a strict Lyapunov function for
`(PV) ẋ^α = Ct α (U^α(x^{−α})) − x^α` on `Σ`. Player 1 is `⟨0, _⟩ : Fin p`. -/
theorem prop41_strictLyapunov (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hpot : IsPotentialGame u)
    (V : (α : Fin p) → (Fin (n α) → ℝ) → ℝ)
    (Ct : (α : Fin p) → (Fin (n α) → ℝ) → (Fin (n α) → ℝ))
    (hV : ∀ α, IsAdmissible (V α)) (hCt : ∀ α, IsPerturbedArgmax (V α) (Ct α)) :
    IsStrictLyapunov (potentialFn V u ⟨0, by omega⟩) (pvField Ct u) (mixedProfiles n) := by sorry

end StochFictPlay.Potential
