-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M4
-- name    : RegretMatching.Main.step_M4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:35.092188+00:00
-- url     : https://prove2.me/theorems/fdf2d81d-4d55-458c-a3df-5242c442878d
-- title:
--   Step M4, Appendix, p. 1145 — P[s_{t+w} = s | h_t] − P[ŝ_{t+w} = s | h_t] = O(w²/t)
-- statement:
--   Fix a finite game with payoff bounds $M^i$ and $\mu>2M^i(m^i-1)$ for all $i$. There is a constant $C$, depending only on the game and $\mu$, such that for every initial mixed action $p_1$, every play of regret matching (2.2) on any probability space, all positive integers $t,w$, every history $h_t$ of positive probability and every $s\in S$,
--   $$\big|P[s_{t+w}=s\mid h_t]-P[\hat s_{t+w}=s\mid h_t]\big|\le C\,\frac{w^2}{t},$$
--   where $\hat s$ is the auxiliary stationary process started at $\hat s_t=s_t$ that uses the transition probabilities $\prod_{i'}\Pi^{i'}_t$ of period $t$ at every later period.
--
--   Over $w$ periods the actual play and the frozen-transition process have nearly the same law when $w$ is small relative to $t$.
--
--   **Formalization Note.** $P[\hat s_{t+w}=s\mid h_t]$ is the $(s_t,s)$ entry of the $w$-th power of the product matrix $\prod_{i'}\Pi^{i'}_t$ (`shatProb`). The constant precedes $p_1$, the probability space and the play.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), pp. 1144–1145, Appendix, the ŝ-process and Step M4; proof p. 1147

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M4
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ) :
    ∃ C : ℝ, ∀ (p₁ : ∀ i, S i → ℝ), (∀ i, p₁ i ∈ stdSimplex ℝ (S i)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (play : ℕ → Ω → (∀ i, S i)), IsPlay (rmMixed u μ p₁) P play →
        ∀ (t w : ℕ) (ht : 1 ≤ t), 1 ≤ w → ∀ h : Fin t → (∀ i, S i),
          P {ω | hist play t ω = h} ≠ 0 → ∀ s : (∀ i, S i),
          |condProb P play h {ω | play (t + w - 1) ω = s}
              - shatProb u μ h (h ⟨t - 1, by omega⟩) w s|
            ≤ C * ((w : ℝ) ^ 2 / t) := by sorry

end RegretMatching.Main
