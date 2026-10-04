-- Prove2me | Theorems.Thm_TheoryOfGames_Minimax_good_iff_saddlePoint
-- name    : TheoryOfGames.Minimax.good_iff_saddlePoint
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:27:40.764974+00:00
-- url     : https://prove2.me/theorems/a3c01445-cb28-43b4-9e1e-9499aedf7866
-- title:
--   (17:C:f) — $\xi \in \bar A$ and $\eta \in \bar B$ iff $\xi, \eta$ is a saddle point of $K$
-- statement:
--   Let $\mathcal H(\tau_1, \tau_2)$ be the matrix of a normalized zero-sum two-person game $\Gamma$, $K(\xi, \eta)$ the bilinear form (17:2), and $\bar A \subseteq S_{\beta_1}$, $\bar B \subseteq S_{\beta_2}$ the sets of good strategies (17:B:a), (17:B:b). For all mixed strategies $\xi \in S_{\beta_1}$ and $\eta \in S_{\beta_2}$,
--   $$\xi \in \bar A \text{ and } \eta \in \bar B \iff \xi, \eta \text{ is a saddle point of } K(\xi, \eta),$$
--   that is, iff $K(\xi', \eta) \le K(\xi, \eta) \le K(\xi, \eta')$ for all $\xi' \in S_{\beta_1}$, $\eta' \in S_{\beta_2}$.
--
--   In the book's words: both players play $\Gamma$ well if and only if $\xi, \eta$ is a saddle point of $K$. It is (13:D*) applied to $K$, which is legitimate because a saddle point of $K$ always exists by the minimax theorem (17:6).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 159, (17:C:f)

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_MixedStrategy

namespace TheoryOfGames.Minimax

/-- (17:C:f), p. 159: for mixed strategies `ξ ∈ S_{β₁}`, `η ∈ S_{β₂}` of the normalized
zero-sum two-person game with matrix `ℋ`, `ξ ∈ Ā` and `η ∈ B̄` if and only if `ξ, η` is a
saddle point of `K(ξ, η)`. -/
theorem good_iff_saddlePoint {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ)
    (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂)) :
    (ξ ∈ goodA H ∧ η ∈ goodB H) ↔ IsMixedSaddlePoint H ξ η := by sorry

end TheoryOfGames.Minimax
