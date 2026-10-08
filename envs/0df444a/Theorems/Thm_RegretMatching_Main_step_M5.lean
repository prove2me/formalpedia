-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M5
-- name    : RegretMatching.Main.step_M5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:28.683917+00:00
-- url     : https://prove2.me/theorems/be8fc254-038e-4d88-ab1b-007c709d3dd2
-- title:
--   Step M5, Appendix, p. 1145 — α_{t,w}(j,s⁻ⁱ) − α̂_{t,w}(j,s⁻ⁱ) = O(w²/t)
-- statement:
--   Fix a finite game with payoff bounds $M^i$ and $\mu>2M^i(m^i-1)$ for all $i$, and fix a player $i$. There is a constant $C$, depending only on the game and $\mu$, such that for every initial mixed action, every play of regret matching (2.2), all positive integers $t,w$, every history $h_t$ of positive probability, every $j\in S^i$ and every $s^{-i}\in S^{-i}$,
--   $$\big|\alpha_{t,w}(j,s^{-i})-\hat\alpha_{t,w}(j,s^{-i})\big|\le C\,\frac{w^2}{t},$$
--   where $\hat\alpha_{t,w}(j,s^{-i})=\sum_{k\in S^i}\Pi_t(k,j)P[\hat s_{t+w}=(k,s^{-i})\mid h_t]-P[\hat s_{t+w}=(j,s^{-i})\mid h_t]$.
--
--   **Formalization Note.** $s^{-i}$ is passed as a full profile whose $i$-th coordinate is ignored. The constant precedes the initial play, the probability space and the play.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1145, Appendix, definition of α̂_{t,w} and Step M5; proof p. 1147

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M5
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) :
    ∃ C : ℝ, ∀ (p₁ : ∀ i, S i → ℝ), (∀ i, p₁ i ∈ stdSimplex ℝ (S i)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (play : ℕ → Ω → (∀ i, S i)), IsPlay (rmMixed u μ p₁) P play →
        ∀ (t w : ℕ) (ht : 1 ≤ t), 1 ≤ w → ∀ h : Fin t → (∀ i, S i),
          P {ω | hist play t ω = h} ≠ 0 → ∀ (j : S i) (s : ∀ i, S i),
          |alpha u μ P play h i w j s - alphaHat u μ h (h ⟨t - 1, by omega⟩) i w j s|
            ≤ C * ((w : ℝ) ^ 2 / t) := by sorry

end RegretMatching.Main
