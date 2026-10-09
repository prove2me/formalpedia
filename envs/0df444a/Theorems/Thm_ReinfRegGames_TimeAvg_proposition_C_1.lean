-- Prove2me | Theorems.Thm_ReinfRegGames_TimeAvg_proposition_C_1
-- name    : ReinfRegGames.TimeAvg.proposition_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:08:03.754261+00:00
-- url     : https://prove2.me/theorems/8d9c0d7f-20d8-4b2d-8477-d53e0764ae70
-- title:
--   Proposition C.1, p. 33 — the choice map Q is Lipschitz and equals the derivative dh* of the convex conjugate
-- statement:
--   Let $B$ be a nonempty finite set, $\Delta = \Delta(B)$ the simplex of probability vectors on $B$, and $h$ a penalty function on $\Delta$ with strong convexity constant $K > 0$ (Definition 2.1). For a score vector $y \in \mathbb R^B$, the choice map $Q(y)$ is the maximizer of $\langle y | x \rangle - h(x)$ over $x \in \Delta$, and $h^*(y) = \max_{x\in\Delta}\{\langle y | x\rangle - h(x)\}$ is the convex conjugate (C.1). Then:
--
--   1. for every $y$ a maximizer $Q(y)$ exists;
--   2. $Q$ is Lipschitz: there is a constant $L$ such that $\|Q(y) - Q(y')\| \le L\,\|y - y'\|$ for all $y, y'$;
--   3. $h^*$ is (Fréchet) differentiable at every $y \in \mathbb R^B$, with
--   $$dh^*(y) = Q(y), \qquad\text{i.e.}\qquad h^*(y + z) = h^*(y) + \langle z | Q(y)\rangle + o(\|z\|).$$
--
--   The identity $Q = dh^*$ is what turns the Fenchel coupling into a Lyapunov-type function along the reinforcement learning dynamics (Lemma C.6); the Lipschitz property makes the trajectory $x(t) = Q(y(t))$ continuous.
--
--   **Formalization Note** The Lipschitz constant is existential, as on the page (which gives none). Distances are those of Lean's sup metric on $\mathbb R^B$; Lipschitz continuity does not depend on the choice of norm. Item 2 implies that the maximizer is unique. The derivative is stated as `HasFDerivAt` with the linear functional $z \mapsto \sum_\beta x_\beta z_\beta$. The hypothesis that $B$ is nonempty is the page's standing assumption that $\Delta$ is the simplex of $\mathbb R^n$, $n \ge 1$ (otherwise no maximizer exists).
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, p. 33, Proposition C.1

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.TimeAvg

theorem proposition_C_1 {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    (h : (B → ℝ) → ℝ) (K : ℝ) (hpen : ReinfRegGames.Extinction.IsPenalty h K) :
    (∀ y : B → ℝ, ∃ x, ReinfRegGames.Extinction.IsChoice h y x) ∧
    (∃ L : ℝ, ∀ y y' x x' : B → ℝ, ReinfRegGames.Extinction.IsChoice h y x → ReinfRegGames.Extinction.IsChoice h y' x' →
      dist x x' ≤ L * dist y y') ∧
    (∀ y x : B → ℝ, ReinfRegGames.Extinction.IsChoice h y x →
      HasFDerivAt (ReinfRegGames.Extinction.conj h) (∑ β, x β • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : B => ℝ) β) y) := by sorry

end ReinfRegGames.TimeAvg
