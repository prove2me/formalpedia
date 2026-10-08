-- Prove2me | Theorems.Thm_RegretMatching_Main_step_M11
-- name    : RegretMatching.Main.step_M11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:07.408603+00:00
-- url     : https://prove2.me/theorems/e8237cee-ec2f-46be-ad36-7a2aec83b669
-- title:
--   Step M11, Appendix, p. 1145 — lim_{t→∞} R_t(j,k) = 0 almost surely
-- statement:
--   Fix a finite game with payoff bounds $M^i$ and $\mu>2M^i(m^i-1)$ for all $i$, an initial mixed action $p_1$, and a play of regret matching (2.2) on a probability space $(\Omega,P)$. Then for every player $i$ and all $j,k\in S^i$,
--   $$\lim_{t\to\infty}R^i_t(j,k)=0\qquad\text{almost surely.}$$
--
--   Every regret of every player vanishes. Together with the PROPOSITION (with $\varepsilon=0$) this gives the Main Theorem.
--
--   **Formalization Note.** The sequence is indexed as $t\mapsto R_{t+1}$, $t=0,1,\dots$ The paper takes $(j,k)\in L$, i.e. $j\ne k$; for $j=k$ the regret is identically $0$, so the statement is given for all $j,k$.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1145, Appendix, Step M11; proof p. 1149

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem step_M11
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (p₁ : ∀ i, S i → ℝ) (hp₁ : ∀ i, p₁ i ∈ stdSimplex ℝ (S i))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → (∀ i, S i)) (hplay : IsPlay (rmMixed u μ p₁) P play)
    (i : ι) (j k : S i) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℕ => regretR u (hist play (t + 1) ω) i j k) atTop (𝓝 0) := by sorry

end RegretMatching.Main
