-- Prove2me | Theorems.Thm_PercolationGames_value_sub_le_of_eqOn_hyperplane
-- name    : PercolationGames.value_sub_le_of_eqOn_hyperplane
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:23.029545+00:00
-- url     : https://prove2.me/theorems/d17095a4-0484-48ec-8186-6e445c48a141
-- title:
--   pp.4–5 — changing the payoff on one hyperplane $\{z\cdot u=h\}$ moves $\gamma_n$ and $v_n$ by at most $c/n$
-- statement:
--   Let $u\in\mathbb Z^d$ satisfy $q(i,j)\cdot u>0$ for all $(i,j)$ (orientation), let $h_0\in\mathbb Z$ and $H=\{z:z\cdot u=h_0\}$. Let $G,G'$ be payoff functions that agree off $H$ and satisfy $|G'(z,i,j)-G(z,i,j)|\le c$ on $H$, with $c\ge0$. Then for every $n\ge1$, every initial state $z$ and all strategies $\sigma,\tau$,
--
--   $$|\gamma'_n(z,\sigma,\tau)-\gamma_n(z,\sigma,\tau)|\le\frac cn,\qquad\text{hence}\qquad|v'_n(z)-v_n(z)|\le\frac cn.$$
--
--   The reason is that $z_m\cdot u$ is strictly increasing along every play, so a play visits $H$ at most once. In the paper $G'$ is $g_\omega$ set to $0$ on the hyperplane $H_{r+1}$ and $c=\|g\|_\infty$; this is the step behind the martingale-increment bound (3.1).
--
--   Differences from the source:
--   - generalization: g′ = g set to 0 on H_{r+1}, bound ‖g‖_∞, initial state 0, P-a.s. → any G, G′ agreeing off H with |G′ − G| ≤ c on H, any c ≥ 0, any initial state z, deterministic; reason: the argument uses only that a play meets H at most once; the paper's g′_ω, g_ω with c = ‖g‖_∞ and z = 0 are an instance for each ω
--   - generalization: |v′_n(0) − v_n(0)| ≤ ‖g‖_∞ (printed) → |v′_n(z) − v_n(z)| ≤ c/n; reason: the printed bound drops the /n of the preceding line (a slip, the /n form is what (3.1) uses); the /n bound implies the printed one for n ≥ 1
--   - encoding: Γ oriented → an explicit witness u with q(i,j)·u > 0 for all i, j; reason: H is defined from that u on p.4
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, pp.4–5 (the auxiliary game Γ′ and the displays "|γ′ω_n(0,σ,τ) − γω_n(0,σ,τ)| ≤ ‖g‖_∞/n, hence |v′_n(0) − v_n(0)| ≤ ‖g‖_∞")

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- Changing the payoff on one hyperplane. Let `u` witness orientation (`q(i, j) · u > 0` for all
`i, j`), let `H := {z | z · u = h₀}`, and let `G, G'` be payoff functions that agree off `H` and
differ by at most `c ≥ 0` on `H`. Every play visits `H` at most once, so for `n ≥ 1`, every initial
state `z` and all strategies, `|γ'_n(z, σ, τ) − γ_n(z, σ, τ)| ≤ c / n`, hence
`|v'_n(z) − v_n(z)| ≤ c / n`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, pp.4–5 (the auxiliary game `Γ'`, with `g' = 0` on `H_{r+1}` and
`c = ‖g‖_∞`).

**Formalization Note.** Deterministic (one `ω`). The paper's `G'` is `G` set to `0` on the
hyperplane, with `c = ‖g‖_∞` and `z = 0`; here `G'` is any function agreeing with `G` off `H`.
The paper prints the value bound as `≤ ‖g‖_∞`; the `/ n` form is what the preceding line gives and
what (3.1) uses. -/
theorem value_sub_le_of_eqOn_hyperplane {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (q : I → J → Site d) (u : Site d) (hu : ∀ i j, 0 < dot (q i j) u) (h₀ : ℤ)
    (G G' : Site d → I → J → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hoff : ∀ z, dot z u ≠ h₀ → ∀ i j, G' z i j = G z i j)
    (hon : ∀ z, dot z u = h₀ → ∀ i j, |G' z i j - G z i j| ≤ c)
    (n : ℕ) (hn : 1 ≤ n) (z : Site d) :
    (∀ (σ : Strategy1 d I J) (τ : Strategy2 d I J),
        |gamma q G' n z σ τ - gamma q G n z σ τ| ≤ c / n) ∧
      |value q G' n z - value q G n z| ≤ c / n := by sorry

end PercolationGames
