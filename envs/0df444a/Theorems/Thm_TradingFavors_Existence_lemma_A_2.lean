-- Prove2me | Theorems.Thm_TradingFavors_Existence_lemma_A_2
-- name    : TradingFavors.Existence.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:28:16.913308+00:00
-- url     : https://prove2.me/theorems/3c4dfb1c-0cf2-4a0a-9d6d-28486d68a045
-- title:
--   Lemma A.2, p. A4 (PDF 34) — v₁(k) ∈ [r̲₁/(1−α₁), r̄₁/(1−β₂)] and r̲₁/(1−α₁) < πᴺᶜ₁(1)
-- statement:
--   Under the standing assumptions, for every trading-favors profile $\sigma$ (equilibrium or not) and every $k\in\mathbb Z$,
--   $$
--   \underline v_1\le v_1(k\mid\sigma)\le\overline v_1,\qquad \underline v_1=\frac{\underline r_1}{1-\alpha_1},\quad \overline v_1=\frac{\overline r_1}{1-\beta_2},
--   $$
--   and moreover $\underline v_1<\pi_1^{NC}(1)$.
--
--   The bounds are the values of the two extreme one-sided profiles; they are used to show monotonicity of the equilibrium payoffs (Proposition 4).
-- source:
--   Hu & Caldentey, Trust and Reciprocity in Firms’ Capacity Sharing, SSRN 4348127 (version of February 6, 2023), p. A4 (PDF 34), Lemma A.2

import Mathlib
import Definitions.Def_TradingFavors_Existence_Model

namespace TradingFavors.Existence

theorem lemma_A_2 (θ : Params) (hθ : θ.Standing) (σ : Profile) (k : ℤ) :
    rLow1 θ / (1 - alpha1 θ) ≤ v1 θ σ k ∧ v1 θ σ k ≤ rBar1 θ / (1 - beta2 θ) ∧
    rLow1 θ / (1 - alpha1 θ) < piNC1 θ 1 := by sorry

end TradingFavors.Existence
