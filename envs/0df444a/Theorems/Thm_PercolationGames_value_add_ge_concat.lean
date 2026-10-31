-- Prove2me | Theorems.Thm_PercolationGames_value_add_ge_concat
-- name    : PercolationGames.value_add_ge_concat
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:29.101165+00:00
-- url     : https://prove2.me/theorems/81e1e9cc-1dff-440c-b6b7-44228054ef8c
-- title:
--   p.6 — concatenation: $v_{m+n}(0)\ge\frac m{m+n}v_m(0)+\frac n{m+n}\min_{z\in\mathcal C}v_n(z)$, and the symmetric bound (corrected: symmetric cube)
-- statement:
--   Let $I,J$ be finite nonempty, $q$ a transition function and $G$ any payoff function. For all $n\ge1$ and $m\in[1..n]$,
--
--   $$\frac m{m+n}v_m(0)+\frac n{m+n}\min_{z\in\mathcal C_n}v_n(z)\le v_{m+n}(0)\le\frac m{m+n}v_m(0)+\frac n{m+n}\max_{z\in\mathcal C_n}v_n(z),$$
--
--   where $\mathcal C_n=[-n\|q\|_\infty..n\|q\|_\infty]^d$.
--
--   For the lower bound, Player 1 plays optimally in the $m$-stage game from $0$ and then optimally in the $n$-stage game from the state $z_{m+1}$, which lies in $\mathcal C_m\subseteq\mathcal C_n$; this strategy guarantees the left-hand side. The upper bound is the same construction for Player 2. Taking expectations gives (3.3).
--
--   Differences from the source:
--   - correction: 𝒞 := [0..n‖q‖_∞]^d (p.4) → the symmetric cube [−n‖q‖_∞..n‖q‖_∞]^d (`cube q n`); reason: with the printed cube the guarantee is false: d = 1, one action each, q = −1, u = −1, i.i.d. Rademacher payoffs, m = n = 1; on the event g(0) = g(1) = 1, g(−1) = −1, of probability 1/8, v_2(0) = 0 < 1 = ½v_1(0) + ½ min_{z∈{0,1}} v_1(z); the play from 0 reaches negative coordinates, and p.5 counts |𝒞| = (2n‖q‖_∞+1)^d, which is the symmetric cube
--   - generalization: P-a.s., for the random payoff g_ω → every payoff function G (deterministic); reason: the argument is a strategy construction for a fixed payoff; each g_ω is an instance
--   - reading: this strategy guarantees m/(m+n) v_m(0) + n/(m+n) min_{z∈𝒞} v_n(z) → v_{m+n}(0) ≥ m/(m+n) v_m(0) + n/(m+n) min_{z∈𝒞_n} v_n(z); reason: a strategy guaranteeing x means the max-min value is at least x; that is how (3.3) uses it
--   - generalization: Player 1's guarantee → Player 1's lower bound and Player 2's upper bound with the max over 𝒞_n; reason: the upper bound is the role switch of p.6; the lower bound is the printed statement
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, p.6 ("Consider the (m + n)-stage game starting from 0 … this strategy guarantees m/(m+n) v_m(0) + n/(m+n) min_{z∈𝒞} v_n(z) P-a.s.")

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- The concatenation guarantee. For `1 ≤ m ≤ n`, Player 1 can play optimally in the `m`-stage
game from `0` and then optimally in the `n`-stage game from `z_{m+1} ∈ 𝒞_n`, so
`v_{m+n}(0) ≥ (m/(m+n)) v_m(0) + (n/(m+n)) min_{z ∈ 𝒞_n} v_n(z)`; symmetrically for Player 2,
`v_{m+n}(0) ≤ (m/(m+n)) v_m(0) + (n/(m+n)) max_{z ∈ 𝒞_n} v_n(z)`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, p.6 ("Consider the (m + n)-stage game starting from 0 …").

**Formalization Note.** Deterministic: holds for every payoff function `G` (every `ω`).
Corrected: `𝒞_n` is the symmetric cube; with the printed `[0..n‖q‖_∞]^d` the guarantee is false
(`d = 1`, one action each, `q = −1`, Rademacher payoffs, `m = n = 1`). The upper bound is Player 2's side ("Switching Players 1 and 2's
roles", p.6). -/
theorem value_add_ge_concat {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (q : I → J → Site d) (G : Site d → I → J → ℝ) (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    (m : ℝ) / ((m : ℝ) + n) * value q G m 0 + (n : ℝ) / ((m : ℝ) + n) * cubeMin q G n
        ≤ value q G (m + n) 0 ∧
      value q G (m + n) 0
        ≤ (m : ℝ) / ((m : ℝ) + n) * value q G m 0 + (n : ℝ) / ((m : ℝ) + n) * cubeMax q G n := by sorry

end PercolationGames
