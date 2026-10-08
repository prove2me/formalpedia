-- Prove2me | Theorems.Thm_RegretMatching_Main_proposition
-- name    : RegretMatching.Main.proposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:00.255412+00:00
-- url     : https://prove2.me/theorems/f0863777-f4e1-4a06-8aac-f9c5edde12ca
-- title:
--   PROPOSITION (§3), pp. 1133–1134 — limsup R_t(j,k) ≤ ε for all i and j ≠ k iff z_t converges to the set of correlated ε-equilibria
-- statement:
--   Let $(s_t)_{t=1,2,\dots}$ be any sequence of plays in a finite game ($s_t\in S$ for all $t$) and let $\varepsilon\ge0$. Then the following are equivalent:
--
--   1. $\limsup_{t\to\infty}R^i_t(j,k)\le\varepsilon$ for every player $i$ and all $j,k\in S^i$ with $j\ne k$;
--   2. the empirical distributions $z_t$ of (2.3) converge to the set of correlated $\varepsilon$-equilibria: for every $\delta>0$ there is $T$ such that for every $t>T$ some correlated $\varepsilon$-equilibrium $\psi$ satisfies
--   $$\operatorname{dist}(z_t,\psi)<\delta .$$
--
--   The statement is deterministic and connects regrets with correlated equilibria: all regrets vanish in the limit exactly when play is empirically close to the set of correlated equilibria (case $\varepsilon=0$; footnote 11: both $\varepsilon>0$ and $\varepsilon=0$ are included).
--
--   **Formalization Note.** "$\limsup_t R_t\le\varepsilon$" is stated as: for every $\delta>0$, eventually $R_t\le\varepsilon+\delta$. This is the same condition and avoids Lean's junk value for the real `limsup` of an unbounded sequence. Convergence to the set uses the paper's own reformulation (p. 1131). $\operatorname{dist}$ is the sup distance on $\mathbb R^S$; any norm gives the same notion. Sequences are 0-based (`x τ` is $s_{\tau+1}$), and $R$ is evaluated at $t+1$.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), pp. 1133–1134, §3, PROPOSITION and footnote 11; p. 1131 (reformulation of convergence to a set)

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace RegretMatching.Main

theorem proposition
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ℕ → (∀ i, S i)) (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ (i : ι) (j k : S i), j ≠ k → ∀ δ : ℝ, 0 < δ →
        ∀ᶠ t in atTop, regretR u (fun τ : Fin (t + 1) => x τ) i j k ≤ ε + δ) ↔
      (∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ t : ℕ, T < t →
        ∃ ψ : (∀ i, S i) → ℝ, IsCorrEq u ε ψ ∧ dist (empDist (fun τ : Fin t => x τ)) ψ < δ) := by sorry

end RegretMatching.Main
