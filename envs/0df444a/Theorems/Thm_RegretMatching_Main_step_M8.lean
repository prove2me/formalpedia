-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M8
-- name    : RegretMatching.Main.step_M8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:04.442923+00:00
-- url     : https://prove2.me/theorems/382b73e6-b144-455e-93fa-a652dea2c602
-- title:
--   Step M8, Appendix, p. 1145 — E[(t+v)²ρ_{t+v} | h_t] ≤ t²ρ_t + O(v³ + t v^{1/2})
-- statement:
--   Fix a finite game with payoff bounds $M^i$ and $\mu>2M^i(m^i-1)$ for all $i$, and fix a player $i$. There is a constant $C$, depending only on the game and $\mu$, such that for every initial mixed action, every play of regret matching (2.2) on any probability space, all positive integers $t,v$ and every history $h_t$ of positive probability,
--   $$E\big[(t+v)^2\rho_{t+v}\mid h_t\big]\le t^2\rho_t+C\,\big(v^3+t\,v^{1/2}\big).$$
--
--   This is the final recursive inequality for the squared distance of the regret vector to the nonpositive orthant.
--
--   **Formalization Note.** The one-sided $O(\cdot)$ is a single constant chosen before the initial play, the probability space and the play.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1145, Appendix, Step M8; proof p. 1149

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M8
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) :
    ∃ C : ℝ, ∀ (p₁ : ∀ i, S i → ℝ), (∀ i, p₁ i ∈ stdSimplex ℝ (S i)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (play : ℕ → Ω → (∀ i, S i)), IsPlay (rmMixed u μ p₁) P play →
        ∀ (t v : ℕ), 1 ≤ t → 1 ≤ v → ∀ h : Fin t → (∀ i, S i),
          P {ω | hist play t ω = h} ≠ 0 →
          condExpHist P play h (fun ω => ((t + v : ℕ) : ℝ) ^ 2 * rho u i (hist play (t + v) ω))
            ≤ (t : ℝ) ^ 2 * rho u i h + C * ((v : ℝ) ^ 3 + t * Real.sqrt v) := by sorry

end RegretMatching.Main
