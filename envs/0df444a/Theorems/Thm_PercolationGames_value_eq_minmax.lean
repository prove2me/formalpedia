-- Prove2me | Theorems.Thm_PercolationGames_value_eq_minmax
-- name    : PercolationGames.value_eq_minmax
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:33.080616+00:00
-- url     : https://prove2.me/theorems/755aaf89-f035-4acc-9e08-58e15917101a
-- title:
--   §2, p.3 — the $n$-stage game has a value: $\max_\sigma\min_\tau\gamma_n=\min_\tau\max_\sigma\gamma_n$, attained
-- statement:
--   Let $I,J$ be finite nonempty action sets, $q:I\times J\to\mathbb Z^d$ a transition function and $G:\mathbb Z^d\times I\times J\to\mathbb R$ any payoff function. For every $n$ and every initial state $z$ there are pure strategies $\sigma^*,\tau^*$ forming a saddle point,
--
--   $$\gamma_n(z,\sigma,\tau^*)\le\gamma_n(z,\sigma^*,\tau^*)\le\gamma_n(z,\sigma^*,\tau)\quad\text{for all }\sigma,\tau,$$
--
--   and
--
--   $$v_n(z)=\max_{\sigma}\min_{\tau}\gamma_n(z,\sigma,\tau)=\min_{\tau}\max_{\sigma}\gamma_n(z,\sigma,\tau)=\gamma_n(z,\sigma^*,\tau^*).$$
--
--   Because Player 2 observes Player 1's current action, the $n$-stage game is a finite game of perfect information, and the value exists in pure strategies. Every later statement uses $v_n(z)$ as a max–min that is attained by optimal strategies.
--
--   Differences from the source:
--   - generalization: the payoff g_ω of the random game (bounded, for each ω) → any payoff function G : ℤ^d → I → J → ℝ; reason: the argument (backward induction over finitely many reachable histories) uses no bound; each g_ω is an instance
--   - generalization: n-stage games, n ≥ 1 → every n ∈ ℕ; reason: at n = 0 the payoff is 0 for all strategies and the statement is trivial; it specializes to n ≥ 1
--   - encoding: max/min → ⨆/⨅ together with the saddle-point inequalities; reason: the saddle-point conjuncts assert attainment, so ⨆/⨅ are the printed max/min
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §2, display defining v^ω_n(z), p.3

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- The `n`-stage game has a value: there is a pure saddle point `(σ*, τ*)`, and
`v_n(z) = max_σ min_τ γ_n(z, σ, τ) = min_τ max_σ γ_n(z, σ, τ) = γ_n(z, σ*, τ*)`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §2, display defining `v^ω_n(z)`, p.3.

**Formalization Note.** Stated for one payoff function `G` (one `ω`), any `G` (not only bounded
ones), any `n` and any initial state `z`. The max and min are `⨆`/`⨅` over pure history-dependent
strategies; the first two conjuncts are the saddle-point inequalities, which give attainment. -/
theorem value_eq_minmax {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (q : I → J → Site d) (G : Site d → I → J → ℝ) (n : ℕ) (z : Site d) :
    ∃ (σs : Strategy1 d I J) (τs : Strategy2 d I J),
      (∀ σ : Strategy1 d I J, gamma q G n z σ τs ≤ gamma q G n z σs τs) ∧
      (∀ τ : Strategy2 d I J, gamma q G n z σs τs ≤ gamma q G n z σs τ) ∧
      value q G n z = gamma q G n z σs τs ∧
      value q G n z = ⨅ τ : Strategy2 d I J, ⨆ σ : Strategy1 d I J, gamma q G n z σ τ := by sorry

end PercolationGames
