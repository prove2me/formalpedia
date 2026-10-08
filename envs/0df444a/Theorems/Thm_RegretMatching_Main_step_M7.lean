-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M7
-- name    : RegretMatching.Main.step_M7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:49.558815+00:00
-- url     : https://prove2.me/theorems/18525753-1ff2-47a8-977b-e8878c1962cc
-- title:
--   Step M7, Appendix, p. 1145 — α̂_{t,w}(j,s⁻ⁱ) = O(w^{−1/2})
-- statement:
--   Fix a finite game with payoff bounds $M^i$ and $\mu>2M^i(m^i-1)$ for all $i$, and fix a player $i$. There is a constant $C$, depending only on the game and $\mu$, such that for all positive integers $t,w$, every history $h_t$, every $j\in S^i$ and every $s^{-i}\in S^{-i}$,
--   $$\big|\hat\alpha_{t,w}(j,s^{-i})\big|\le\frac{C}{\sqrt w}.$$
--
--   **Formalization Note.** The page prints $\hat\alpha_{t,w}(j,s^{-1})$, a misprint for $s^{-i}$. The statement is deterministic: $\hat\alpha$ depends only on the history, and the bound is uniform over all histories.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1145, Appendix, Step M7; proof p. 1148

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M7
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) :
    ∃ C : ℝ, ∀ (t w : ℕ) (ht : 1 ≤ t), 1 ≤ w → ∀ (h : Fin t → (∀ i, S i)) (j : S i)
        (s : ∀ i, S i),
      |alphaHat u μ h (h ⟨t - 1, by omega⟩) i w j s| ≤ C / Real.sqrt w := by sorry

end RegretMatching.Main
