-- Prove2me | Theorems.Thm_TheoryOfGames_Minimax_speciallyStrictlyDetermined_iff_pure_good
-- name    : TheoryOfGames.Minimax.speciallyStrictlyDetermined_iff_pure_good
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:32:49.972151+00:00
-- url     : https://prove2.me/theorems/5991d2b4-f0fe-41dc-a2a8-32817b6d8e65
-- title:
--   (17:E) — specially strictly determined iff both players have a pure good strategy
-- statement:
--   Let $\mathcal H(\tau_1, \tau_2)$ be the matrix of a normalized zero-sum two-person game $\Gamma$ with $\beta_1 \ge 1$ and $\beta_2 \ge 1$ pure strategies. The game is specially strictly determined, i.e.
--   $$v_1 = \operatorname{Max}_{\tau_1} \operatorname{Min}_{\tau_2} \mathcal H(\tau_1, \tau_2) = \operatorname{Min}_{\tau_2} \operatorname{Max}_{\tau_1} \mathcal H(\tau_1, \tau_2) = v_2,$$
--   if and only if there exists for each player a good strategy which is a pure strategy: some coordinate vector $\delta^{\tau_1}$ belongs to $\bar A$ and some coordinate vector $\delta^{\tau_2}$ belongs to $\bar B$.
--
--   The result ties the pure-strategy notion of strict determinateness of §14 to the mixed-strategy solution of §17.
--
--   **Formalization Note** $\delta^{\tau}$ is `pureVec τ`, the vector with a $1$ in coordinate $\tau$ and $0$ elsewhere; pure strategies are indexed from $0$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 161, (17:E); definition of special strict determinateness p. 150, 17.5.1

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_MixedStrategy

namespace TheoryOfGames.Minimax

/-- (17:E), p. 161: a normalized zero-sum two-person game with `β₁, β₂ ≥ 1` pure strategies is
specially strictly determined (`v₁ = v₂`, 17.5.1) if and only if each player has a good
strategy which is a pure strategy: some `δ^{τ₁}` belongs to `Ā` and some `δ^{τ₂}` belongs
to `B̄`. -/
theorem speciallyStrictlyDetermined_iff_pure_good {β₁ β₂ : ℕ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (H : Fin β₁ → Fin β₂ → ℝ) :
    SpeciallyStrictlyDetermined H ↔
      (∃ τ₁ : Fin β₁, pureVec τ₁ ∈ goodA H) ∧ (∃ τ₂ : Fin β₂, pureVec τ₂ ∈ goodB H) := by sorry

end TheoryOfGames.Minimax
