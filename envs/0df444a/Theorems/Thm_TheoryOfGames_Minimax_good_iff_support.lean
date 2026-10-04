-- Prove2me | Theorems.Thm_TheoryOfGames_Minimax_good_iff_support
-- name    : TheoryOfGames.Minimax.good_iff_support
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T03:30:50.199987+00:00
-- url     : https://prove2.me/theorems/1f5f4bed-0e45-4fa7-becc-7ecfba0f1c35
-- title:
--   (17:D) — good strategies characterized by their supports
-- statement:
--   Let $\mathcal H(\tau_1, \tau_2)$, $\tau_1 = 1, \dots, \beta_1$, $\tau_2 = 1, \dots, \beta_2$, be the matrix of a normalized zero-sum two-person game $\Gamma$, and let $\bar A \subseteq S_{\beta_1}$, $\bar B \subseteq S_{\beta_2}$ be the sets of good strategies of players 1 and 2 (17:B:a), (17:B:b). For all mixed strategies $\xi \in S_{\beta_1}$ and $\eta \in S_{\beta_2}$, $\xi \in \bar A$ and $\eta \in \bar B$ if and only if both of the following are true:
--
--   1. for each $\tau_1$ for which $\sum_{\tau_2=1}^{\beta_2} \mathcal H(\tau_1, \tau_2)\, \eta_{\tau_2}$ does not assume its maximum (in $\tau_1$), we have $\xi_{\tau_1} = 0$;
--   2. for each $\tau_2$ for which $\sum_{\tau_1=1}^{\beta_1} \mathcal H(\tau_1, \tau_2)\, \xi_{\tau_1}$ does not assume its minimum (in $\tau_2$), we have $\eta_{\tau_2} = 0$.
--
--   In symbols, the right-hand side is
--   $$\Big(\exists \tau_1' : \textstyle\sum_{\tau_2} \mathcal H(\tau_1', \tau_2)\eta_{\tau_2} > \sum_{\tau_2} \mathcal H(\tau_1, \tau_2)\eta_{\tau_2}\Big) \Rightarrow \xi_{\tau_1} = 0, \qquad \Big(\exists \tau_2' : \textstyle\sum_{\tau_1} \mathcal H(\tau_1, \tau_2')\xi_{\tau_1} < \sum_{\tau_1} \mathcal H(\tau_1, \tau_2)\xi_{\tau_1}\Big) \Rightarrow \eta_{\tau_2} = 0.$$
--
--   Verbally (the book, p. 161): if $\xi, \eta$ are good mixed strategies, then $\xi$ excludes every pure strategy $\tau_1$ that is not optimal against $\eta$, and $\eta$ excludes every $\tau_2$ that is not optimal against $\xi$; and conversely, a pair with this property is a pair of good strategies. This is the complementary-slackness description of the optimal strategy pairs of a matrix game.
--
--   **Formalization Note** Pure strategies are indexed from $0$ (`Fin β₁`, `Fin β₂`); $S_\beta$ is `stdSimplex ℝ (Fin β)`. "Does not assume its maximum at $\tau_1$" is written as the negation of "$\sum_{\tau_2}\mathcal H(\tau_1', \tau_2)\eta_{\tau_2} \le \sum_{\tau_2}\mathcal H(\tau_1, \tau_2)\eta_{\tau_2}$ for every $\tau_1'$", which involves no Max operator and no junk value. The hypotheses $\xi \in S_{\beta_1}$, $\eta \in S_{\beta_2}$ force $\beta_1, \beta_2 \ge 1$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 161, (17:D)

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_MixedStrategy

namespace TheoryOfGames.Minimax

/-- (17:D), p. 161: for mixed strategies `ξ ∈ S_{β₁}`, `η ∈ S_{β₂}` of the normalized zero-sum
two-person game with matrix `ℋ`, `ξ ∈ Ā` and `η ∈ B̄` if and only if
* for each `τ₁` at which `∑_{τ₂} ℋ(τ₁, τ₂) η_{τ₂}` does not assume its maximum (in `τ₁`),
  `ξ_{τ₁} = 0`; and
* for each `τ₂` at which `∑_{τ₁} ℋ(τ₁, τ₂) ξ_{τ₁}` does not assume its minimum (in `τ₂`),
  `η_{τ₂} = 0`. -/
theorem good_iff_support {β₁ β₂ : ℕ} (H : Fin β₁ → Fin β₂ → ℝ)
    (ξ : Fin β₁ → ℝ) (η : Fin β₂ → ℝ)
    (hξ : ξ ∈ stdSimplex ℝ (Fin β₁)) (hη : η ∈ stdSimplex ℝ (Fin β₂)) :
    (ξ ∈ goodA H ∧ η ∈ goodB H) ↔
      ((∀ τ₁, ¬ (∀ τ₁', ∑ τ₂, H τ₁' τ₂ * η τ₂ ≤ ∑ τ₂, H τ₁ τ₂ * η τ₂) → ξ τ₁ = 0) ∧
       (∀ τ₂, ¬ (∀ τ₂', ∑ τ₁, H τ₁ τ₂ * ξ τ₁ ≤ ∑ τ₁, H τ₁ τ₂' * ξ τ₁) → η τ₂ = 0)) := by sorry

end TheoryOfGames.Minimax
