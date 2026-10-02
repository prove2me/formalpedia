-- Prove2me | Theorems.Thm_TheoryOfGames_Minimax_min_max_K_pure
-- name    : TheoryOfGames.Minimax.min_max_K_pure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T03:18:26.914842+00:00
-- url     : https://prove2.me/theorems/8e176742-3bff-46e5-93b3-673cb5cf4b6e
-- title:
--   (17:A) — $\operatorname{Min}_\eta K(\xi,\eta)$ and $\operatorname{Max}_\xi K(\xi,\eta)$ are attained at pure strategies
-- statement:
--   Let $\mathcal H(\tau_1, \tau_2)$ be the matrix of a normalized zero-sum two-person game with $\beta_1 \ge 1$ and $\beta_2 \ge 1$ pure strategies, and $K(\xi, \eta)$ the bilinear form (17:2). Then:
--
--   1. for every $\xi \in S_{\beta_1}$ the minimum of $K(\xi, \eta)$ over $\eta \in S_{\beta_2}$ exists and
--   $$\operatorname{Min}_\eta K(\xi, \eta) = \operatorname{Min}_{\tau_2} \sum_{\tau_1=1}^{\beta_1} \mathcal H(\tau_1, \tau_2)\, \xi_{\tau_1};$$
--   2. for every $\eta \in S_{\beta_2}$ the maximum of $K(\xi, \eta)$ over $\xi \in S_{\beta_1}$ exists and
--   $$\operatorname{Max}_\xi K(\xi, \eta) = \operatorname{Max}_{\tau_1} \sum_{\tau_2=1}^{\beta_2} \mathcal H(\tau_1, \tau_2)\, \eta_{\tau_2}.$$
--
--   The lemma reduces the inner optimisation over mixed strategies to one over pure strategies; it gives the formulae (17:5:a), (17:5:b) for $v'_1$, $v'_2$ and is used in the characterization (17:D) of good strategies.
--
--   **Formalization Note** "The minimum exists and equals $m$" is `IsLeast` of the image set $\{K(\xi,\eta) : \eta \in S_{\beta_2}\}$ at $m$ (and `IsGreatest` for the maximum). The pure-strategy $\operatorname{Min}_{\tau_2}$ and $\operatorname{Max}_{\tau_1}$ are `⨅`/`⨆` over the nonempty finite index sets `Fin β₂`, `Fin β₁`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 151, (17:A)

import Mathlib
import Definitions.Def_TheoryOfGames_Minimax_MixedStrategy

namespace TheoryOfGames.Minimax

/-- (17:A), p. 151: for every `ξ ∈ S_{β₁}` the minimum of `K(ξ, η)` over `η ∈ S_{β₂}` exists
and equals `Min_{τ₂} ∑_{τ₁} ℋ(τ₁, τ₂) ξ_{τ₁}`; for every `η ∈ S_{β₂}` the maximum of
`K(ξ, η)` over `ξ ∈ S_{β₁}` exists and equals `Max_{τ₁} ∑_{τ₂} ℋ(τ₁, τ₂) η_{τ₂}`.
Both players have at least one pure strategy (`β₁, β₂ ≥ 1`). -/
theorem min_max_K_pure {β₁ β₂ : ℕ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (H : Fin β₁ → Fin β₂ → ℝ) :
    (∀ ξ ∈ stdSimplex ℝ (Fin β₁),
      IsLeast (K H ξ '' stdSimplex ℝ (Fin β₂)) (⨅ τ₂, ∑ τ₁, H τ₁ τ₂ * ξ τ₁)) ∧
    (∀ η ∈ stdSimplex ℝ (Fin β₂),
      IsGreatest ((fun ξ => K H ξ η) '' stdSimplex ℝ (Fin β₁)) (⨆ τ₁, ∑ τ₂, H τ₁ τ₂ * η τ₂)) := by sorry

end TheoryOfGames.Minimax
