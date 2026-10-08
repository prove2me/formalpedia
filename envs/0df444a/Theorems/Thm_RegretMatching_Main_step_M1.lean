-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M1
-- name    : RegretMatching.Main.step_M1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:27.649244+00:00
-- url     : https://prove2.me/theorems/1a77f5c4-052f-49ba-ab24-ca73d1d12476
-- title:
--   Step M1, Appendix, p. 1144 — E[(t+v)²ρ_{t+v}|h_t] ≤ t²ρ_t + 2t Σ_w R_t·E[A_{t+w}|h_t] + O(v²), and (t+v)²ρ_{t+v} − t²ρ_t = O(tv + v²)
-- statement:
--   Fix a finite game with payoff bounds $M^i$ and $\mu>2M^i(m^i-1)$ for all $i$, and fix a player $i$. There is a constant $C$, depending only on the game and $\mu$, such that:
--
--   1. for all positive integers $t,v$ and every history $h_{t+v}$ (with $h_t$ its first $t$ plays),
--   $$\big|(t+v)^2\rho_{t+v}-t^2\rho_t\big|\le C\,(tv+v^2);$$
--   2. for every initial mixed action $p_1$, every play of regret matching (2.2) on any probability space, all positive integers $t,v$ and every history $h_t$ of positive probability,
--   $$E\big[(t+v)^2\rho_{t+v}\mid h_t\big]\le t^2\rho_t+2t\sum_{w=1}^{v}R_t\cdot E[A_{t+w}\mid h_t]+C\,v^2,$$
--   where $R_t\cdot E[A_{t+w}\mid h_t]=\sum_{j\ne k}R_t(j,k)\,E[A_{t+w}(j,k)\mid h_t]$.
--
--   This is the basic recursion for the squared distance of the regret vector to the nonpositive orthant, taken over a block of $v$ periods.
--
--   **Formalization Note.** The paper's $O(\cdot)$ (footnote 34) is encoded as one constant $C$ chosen after the game, $M$, $\mu$ and $i$, and before the initial play, the probability space and the play. Part (ii) is deterministic and holds for every history.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1144, Appendix, Step M1 (i)–(ii); proof p. 1146

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M1
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) :
    ∃ C : ℝ,
      (∀ (t v : ℕ), 1 ≤ t → 1 ≤ v → ∀ h : Fin (t + v) → (∀ i, S i),
        |((t + v : ℕ) : ℝ) ^ 2 * rho u i h
            - (t : ℝ) ^ 2 * rho u i (fun τ : Fin t => h (Fin.castAdd v τ))|
          ≤ C * ((t : ℝ) * v + (v : ℝ) ^ 2)) ∧
      (∀ (p₁ : ∀ i, S i → ℝ), (∀ i, p₁ i ∈ stdSimplex ℝ (S i)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (play : ℕ → Ω → (∀ i, S i)), IsPlay (rmMixed u μ p₁) P play →
        ∀ (t v : ℕ), 1 ≤ t → 1 ≤ v → ∀ h : Fin t → (∀ i, S i),
          P {ω | hist play t ω = h} ≠ 0 →
          condExpHist P play h (fun ω => ((t + v : ℕ) : ℝ) ^ 2 * rho u i (hist play (t + v) ω))
            ≤ (t : ℝ) ^ 2 * rho u i h
              + 2 * t * ∑ w ∈ Finset.Icc 1 v, ∑ p ∈ (Finset.univ : Finset (S i)).offDiag,
                  regretR u h i p.1 p.2 *
                    condExpHist P play h (fun ω => regretA u i (play (t + w - 1) ω) p.1 p.2)
              + C * (v : ℝ) ^ 2) := by sorry

end RegretMatching.Main
