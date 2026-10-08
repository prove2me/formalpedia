-- Prove2me | Theorems.Thm_RegretMatching_Main_main_theorem
-- name    : RegretMatching.Main.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:19.693297+00:00
-- url     : https://prove2.me/theorems/3718c50f-4a76-4f9f-9576-6cd1a93f6fee
-- title:
--   MAIN THEOREM (§2), p. 1131 — under regret-matching (2.2) the empirical distributions z_t converge a.s. to the set of correlated equilibria
-- statement:
--   Let $\Gamma=(N,(S^i),(u^i))$ be a finite game, let $M^i\ge|u^i(\cdot)|$ for every player $i$, and fix $\mu$ with $\mu>2M^i(m^i-1)$ for all $i$, where $m^i=|S^i|$ (footnote 5). Suppose every player plays according to the adaptive procedure (2.2): at time $t+1$ player $i$, whose last strategy was $j=s^i_t$, switches to $k\ne j$ with probability $\frac1\mu R^i_t(j,k)$ and otherwise repeats $j$; the initial mixed actions $p^i_1\in\Delta(S^i)$ are arbitrary, and given the history players randomize independently. Then, almost surely, the empirical distributions of play
--   $$z_t(s)=\frac1t\,|\{\tau\le t:s_\tau=s\}|$$
--   converge to the set of correlated equilibria of $\Gamma$: with probability one, for every $\varepsilon>0$ there is $T_0$ such that for every $t>T_0$ some correlated equilibrium $\psi_t$ satisfies $\operatorname{dist}(z_t,\psi_t)<\varepsilon$.
--
--   The theorem shows that a simple procedure, in which each player looks only at their own payoffs and their own past regrets, leads the empirical distribution of play to the set of correlated equilibria. It does not say that $z_t$ converges to a point.
--
--   **Formalization Note.** The conclusion uses the paper's own reformulation of convergence to a set (p. 1131), so no separate nonemptiness of the correlated-equilibrium set is needed. The statement quantifies over every probability space carrying a play of (2.2) (`IsPlay`), with every player following (2.2). $\operatorname{dist}$ is the sup distance on $\mathbb R^S$. One $\mu$ serves all players, as on p. 1130.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1131, §2, MAIN THEOREM and the reformulation following it; (2.2) and footnote 5, p. 1130

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem main_theorem
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (p₁ : ∀ i, S i → ℝ) (hp₁ : ∀ i, p₁ i ∈ stdSimplex ℝ (S i))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → (∀ i, S i)) (hplay : IsPlay (rmMixed u μ p₁) P play) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ t : ℕ, T < t →
      ∃ ψ : (∀ i, S i) → ℝ, IsCorrEq u 0 ψ ∧ dist (empDist (hist play t ω)) ψ < ε := by sorry

end RegretMatching.Main
