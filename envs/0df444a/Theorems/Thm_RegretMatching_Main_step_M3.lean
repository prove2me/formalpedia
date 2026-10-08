-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M3
-- name    : RegretMatching.Main.step_M3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:39.397738+00:00
-- url     : https://prove2.me/theorems/19967129-6b5c-4c1e-9a48-7a46b8cd20f2
-- title:
--   Step M3, Appendix, p. 1144 — R_{t+v}(j,k) − R_t(j,k) = O(v/t)
-- statement:
--   Fix a finite game with payoff bounds $M^i$ and $\mu>2M^i(m^i-1)$ for all $i$, and fix a player $i$. There is a constant $C$, depending only on the game, such that for all positive integers $t,v$, every history $h_{t+v}$ (with $h_t$ its first $t$ plays) and all $j,k\in S^i$,
--   $$\big|R_{t+v}(j,k)-R_t(j,k)\big|\le C\,\frac{v}{t}.$$
--
--   Regrets move slowly: over $v$ periods they change by at most order $v/t$. This drives the comparison of the actual process with the stationary $\hat s$-process (Step M4).
--
--   **Formalization Note.** Deterministic: the bound holds for every history. The constant is chosen before $t$, $v$ and the history (footnote 34). For $j=k$ both sides are $0$.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1144, Appendix, Step M3; proof p. 1146

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M3
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) :
    ∃ C : ℝ, ∀ (t v : ℕ), 1 ≤ t → 1 ≤ v → ∀ (h : Fin (t + v) → (∀ i, S i)) (j k : S i),
      |regretR u h i j k - regretR u (fun τ : Fin t => h (Fin.castAdd v τ)) i j k|
        ≤ C * ((v : ℝ) / t) := by sorry

end RegretMatching.Main
