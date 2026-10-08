-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M9
-- name    : RegretMatching.Main.step_M9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:00.066024+00:00
-- url     : https://prove2.me/theorems/4b5ca7bd-f90e-458d-a257-43c619d18a32
-- title:
--   Step M9, Appendix, p. 1145 — with t_n = ⌊n^{5/3}⌋, E[t²_{n+1} ρ_{t_{n+1}} | h_{t_n}] ≤ t²_n ρ_{t_n} + O(n²)
-- statement:
--   Let $t_n=\lfloor n^{5/3}\rfloor$ for $n=1,2,\dots$. Fix a finite game with payoff bounds $M^i$ and $\mu>2M^i(m^i-1)$ for all $i$, and fix a player $i$. There is a constant $C$, depending only on the game and $\mu$, such that for every initial mixed action, every play of regret matching (2.2) on any probability space, every $n\ge1$ and every history $h_{t_n}$ of positive probability,
--   $$E\big[t_{n+1}^2\,\rho_{t_{n+1}}\mid h_{t_n}\big]\le t_n^2\,\rho_{t_n}+C\,n^2 .$$
--
--   Along the subsequence $t_n$ the recursion of Step M8 has an error of order $n^2$, small enough for a strong law of large numbers.
--
--   **Formalization Note.** $t_n$ is `⌊(n:ℝ)^(5/3)⌋₊`; $t_1=1$, so every conditioning history is nonempty.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1145, Appendix, definition of t_n and Step M9; proof p. 1149

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M9
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) :
    ∃ C : ℝ, ∀ (p₁ : ∀ i, S i → ℝ), (∀ i, p₁ i ∈ stdSimplex ℝ (S i)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (play : ℕ → Ω → (∀ i, S i)), IsPlay (rmMixed u μ p₁) P play →
        ∀ n : ℕ, 1 ≤ n → ∀ h : Fin (tSeq n) → (∀ i, S i),
          P {ω | hist play (tSeq n) ω = h} ≠ 0 →
          condExpHist P play h
              (fun ω => ((tSeq (n + 1) : ℕ) : ℝ) ^ 2 * rho u i (hist play (tSeq (n + 1)) ω))
            ≤ ((tSeq n : ℕ) : ℝ) ^ 2 * rho u i h + C * (n : ℝ) ^ 2 := by sorry

end RegretMatching.Main
