-- Prove2me | Theorems.Thm_RegretMatching_Approach_theorem_A
-- name    : RegretMatching.Approach.theorem_A
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:55.413239+00:00
-- url     : https://prove2.me/theorems/0b3f135e-c49d-47e5-8b69-560fd1ecda0d
-- title:
--   THEOREM A (§3), p. 1133 — if player i plays a solution of (3.1) every period, all regrets Rⁱ_t(j,k), j ≠ k, converge to 0 a.s.
-- statement:
--   Let $\Gamma$ be a finite game and fix a player $i$. The game is played repeatedly; given the history $h_t$, players randomize independently. Suppose that at every period $t+1$ (for $t\ge1$) player $i$ chooses strategies according to a probability vector $q^i_t\in\Delta(S^i)$ that satisfies (3.1):
--   $$\sum_{k\in S^i}q^i_t(k)R^i_t(k,j)=q^i_t(j)\sum_{k\in S^i}R^i_t(j,k)\qquad\text{for every }j\in S^i,$$
--   with $R^i_t(j,j):=0$. Nothing is assumed about how the other players choose their strategies, and player $i$'s first-period strategy is arbitrary. Then, almost surely,
--   $$R^i_t(j,k)\longrightarrow0\quad(t\to\infty)\qquad\text{for every }j,k\in S^i\text{ with }j\ne k .$$
--
--   By the Proposition of §3, this implies that when every player follows such a procedure, the empirical distributions of play converge almost surely to the set of correlated equilibria (the Corollary).
--
--   **Formalization Note.** Behaviour is a profile $\sigma$ assigning to each period, history and player a probability vector; only player $i$'s component is constrained, by (3.1) at every history of length $t+1\ge1$. The play is any sequence of random variables on any probability space whose conditional law given each positive-probability history is the product of the players' mixed actions. The quantifier "for every $j\ne k$" is placed inside the almost-sure statement, which is equivalent since $S^i$ is finite.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), p. 1133, THEOREM A and REMARK

import Mathlib
import Definitions.Def_RegretMatching_Approach_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Approach

theorem theorem_A
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (i : ι)
    (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i' : ι) → S i' → ℝ)
    (hσ : ∀ (t : ℕ) (h : Fin t → (∀ i, S i)) (i' : ι), σ t h i' ∈ stdSimplex ℝ (S i'))
    (h31 : ∀ (t : ℕ) (h : Fin (t + 1) → (∀ i, S i)), SatisfiesEq31 u h i (σ (t + 1) h i))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (play : ℕ → Ω → (∀ i, S i)) (hplay : RegretMatching.Main.IsPlay σ P play) :
    ∀ᵐ ω ∂P, ∀ j k : S i, j ≠ k →
      Tendsto (fun t : ℕ => RegretMatching.Main.regretR u (hist play (t + 1) ω) i j k) atTop (𝓝 0) := by sorry

end RegretMatching.Approach
