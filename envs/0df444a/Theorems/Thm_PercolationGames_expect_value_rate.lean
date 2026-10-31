-- Prove2me | Theorems.Thm_PercolationGames_expect_value_rate
-- name    : PercolationGames.expect_value_rate
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:33.608648+00:00
-- url     : https://prove2.me/theorems/2732a9fe-7f16-463c-9df0-7a5d424c1d4e
-- title:
--   p.6 — $\mathbb E(v_n)\to v_\infty$ with $|v_\infty-\mathbb E(v_n)|\le A\ln(n+1)^{1/2}n^{-1/2}$
-- statement:
--   Consider an i.i.d., oriented percolation game with uniformly bounded payoffs. Then $\mathbb E(v_n)$ converges to a real number $v_\infty$, and there is $A>0$ such that for all $n\ge1$,
--
--   $$|v_\infty-\mathbb E(v_n)|\le A\ln(n+1)^{1/2}n^{-1/2}.$$
--
--   This is the convergence half of the proof of Theorem 2.3; combined with the concentration bound (3.2) it gives (2.1).
--
--   **Formalization Note** $\mathbb E(v_n)=\int v_n(0)\,d\mathbb P$.
--
--   Differences from the source:
--   - generalization: percolation game with an ergodic measure-preserving ℤ^d-action τ, τ-stationary g, and i.i.d. site vectors (Definition 2.2) → IsIID g μ: each g(z,i,j) measurable, site vectors mutually independent and identically distributed; no τ; reason: i.i.d. site vectors have a translation-invariant law, which is all the proof uses; every i.i.d. percolation game of the paper satisfies IsIID
--   - reading: g uniformly bounded (p.3) → ∃ M, |g ω z i j| ≤ M for all ω, z, i, j; reason: the proof uses ‖g‖_∞ as a deterministic constant, so the bound is uniform in ω
--   - encoding: E(v_n) := E(v_n(0)); P(event) → Bochner integral ∫ v_n(0) dμ; the measure μ of the set (outer measure if it were not measurable); reason: v_n(0) is bounded and measurable (identDistrib_value), so the integral is the expectation; the outer measure is at least the probability
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
--   - reading: ln(n + 1)^{1/2} → (ln(n + 1))^{1/2}, the definition `rate`; reason: p.5 needs this parse: λ_n = 2√2 ln(2n‖q‖_∞+1)^{1/2}(d+1)‖g‖_∞ n^{−1/2} makes λ_n²n/(8‖g‖²_∞) a multiple of ln(2n‖q‖_∞+1); for n ≥ 1 it is at most a constant times ln(n+1), so this is the stronger of the two parses
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, p.6 ("hence E(v_n) converges. Call v_∞ the limit"; display after "Switching Players 1 and 2's roles")

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- The rate of `𝔼(v_n)`. In an i.i.d., oriented, uniformly bounded percolation game, `𝔼(v_n)`
converges to some `v_∞ ∈ ℝ`, and there is `A > 0` with
`|v_∞ − 𝔼(v_n)| ≤ A ln(n+1)^{1/2} n^{−1/2}` for all `n ≥ 1`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, p.6 ("hence 𝔼(v_n) converges. Call v_∞ the limit"; display after
"Switching Players 1 and 2's roles").

**Formalization Note.** `𝔼(v_n) = ∫ v_n(0) dμ`. -/
theorem expect_value_rate {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : I → J → Site d) (g : Ω → Site d → I → J → ℝ) (hiid : IsIID g μ)
    (hbdd : ∃ M : ℝ, ∀ ω z i j, |g ω z i j| ≤ M) (hq : Oriented q) :
    ∃ v : ℝ, ∃ A : ℝ, 0 < A ∧
      Tendsto (fun n : ℕ => (∫ ω', value q (g ω') n 0 ∂μ)) atTop (𝓝 v) ∧
      ∀ n : ℕ, 1 ≤ n → |v - (∫ ω', value q (g ω') n 0 ∂μ)| ≤ A * rate n := by sorry

end PercolationGames
