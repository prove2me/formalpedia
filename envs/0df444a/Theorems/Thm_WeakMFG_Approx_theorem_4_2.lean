-- Prove2me | Theorems.Thm_WeakMFG_Approx_theorem_4_2
-- name    : WeakMFG.Approx.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:29:56.081653+00:00
-- url     : https://prove2.me/theorems/6649de66-2f07-4374-a78f-95a7ac3daa1b
-- title:
--   Theorem 4.2 — the distributed controls $\alpha^i_t=\hat\alpha(t,X^i)$ form an $\epsilon_n$-Nash equilibrium of the $n$-player game, $\epsilon_n\to0$
-- statement:
--   Assume (S), (C) and (F) hold, and let $(\hat\mu,\hat q)$ be a solution of the mean field game with corresponding closed-loop control $\hat\alpha=\hat\alpha(t,x)$. In the $n$-player game of §4, the strategies $\alpha^i_t:=\hat\alpha(t,X^i)$ form an approximate Nash equilibrium: there is a sequence $\epsilon_n\ge0$ with $\epsilon_n\to0$ such that, for every $n\ge1$, every $1\le i\le n$ and every $\beta\in\mathbb A_n$,
--   $$J_{n,i}(\alpha^1,\dots,\alpha^{i-1},\beta,\alpha^{i+1},\dots,\alpha^n)\ \le\ J_{n,i}(\alpha^1,\dots,\alpha^n)+\epsilon_n.$$
--
--   Each $\alpha^i$ uses only player $i$'s own state, while the deviation $\beta$ may use the states of all $n$ players; the theorem says that full information gains a deviating player at most $\epsilon_n$, uniformly over players and deviations. It is the justification of the mean field game as an approximation of large symmetric stochastic differential games.
--
--   **Formalization Note** The sequence $\epsilon$ is chosen before $n$, $i$ and $\beta$. Players are indexed $0,\dots,n-1$. Both values are computed with every version of the corresponding densities $dP_n(\cdot)/dP$, and versions exist. All hypotheses (the mean field data with (S), (C), (F), the solution and its closed-loop control, and the game space) are bundled in the structure of the game definition.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Theorem 4.2, §4, p. 13

import Mathlib
import Definitions.Def_WeakMFG_Approx_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace WeakMFG.Approx

variable {d : ℕ} {T : ℝ≥0} {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [MeasurableSpace EA] [BorelSpace EA] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {B : Base d Ω} {ψ : WeakMFG.Existence.Path d T → ℝ} {A : Set EA}
  {σ : ℝ≥0 → WeakMFG.Existence.Path d T → Matrix (Fin d) (Fin d) ℝ}
  {b : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → EA → (Fin d → ℝ)}
  {f : ℝ≥0 → WeakMFG.Existence.Path d T → Ppsi ψ → PA A → EA → ℝ} {g : WeakMFG.Existence.Path d T → Ppsi ψ → ℝ}

/-- Theorem 4.2 (Carmona–Lacker, arXiv:1307.1152v2, §4, p. 13). Assume (C) and (F) hold (and (S)),
and let `(μ̂, q̂)` be a solution of the MFG with closed-loop control `α̂ = α̂(t, x)` (Remark 3.2) — all
bundled in `G : Game …`. Then the distributed strategies `αⁱ_t := α̂(t, Xⁱ)` form an approximate Nash
equilibrium of the `n`-player game: there is a sequence `ε_n ≥ 0` with `ε_n → 0` such that for
`1 ≤ i ≤ n` and `β ∈ 𝔸_n`,
`J_{n,i}(α¹, …, α^{i−1}, β, α^{i+1}, …, αⁿ) ≤ J_{n,i}(α¹, …, αⁿ) + ε_n`.
Formalization Note: players are `i : Fin n` (D7); the sequence `ε` is chosen before `n`, `i`, `β`;
both sides are evaluated with every version of the respective densities `dP_n(·)/dP`, and versions
exist (D6). -/
theorem theorem_4_2 (G : Game B Ω' ψ A σ b f g) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ (n : ℕ) [NeZero n] (i : Fin n) (β : ℝ≥0 → Ω' → A), G.IsAdmissibleN n β →
        (∃ D, G.IsDensityN n (Function.update (G.αn n) i β) D) ∧
        (∃ D, G.IsDensityN n (G.αn n) D) ∧
        ∀ Ddev Deq, G.IsDensityN n (Function.update (G.αn n) i β) Ddev →
          G.IsDensityN n (G.αn n) Deq →
          G.JN n i (Function.update (G.αn n) i β) Ddev ≤ G.JN n i (G.αn n) Deq + ε n := by sorry

end WeakMFG.Approx
