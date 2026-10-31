-- Prove2me | Theorems.Thm_PercolationGames_expect_min_cube_ge
-- name    : PercolationGames.expect_min_cube_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:26.922992+00:00
-- url     : https://prove2.me/theorems/2365c80c-568b-4216-ab02-032ca1c81bc6
-- title:
--   p.6 — $\mathbb E(\min_{z\in\mathcal C}v_n(z))\ge\mathbb E(v_n)-D\ln(n+1)^{1/2}n^{-1/2}$, and the symmetric bound for the max
-- statement:
--   Consider an i.i.d., oriented percolation game with uniformly bounded payoffs, and let $\mathcal C_n=[-n\|q\|_\infty..n\|q\|_\infty]^d$. There is $D>0$ such that for all $n\ge1$,
--
--   $$\mathbb E\Bigl(\min_{z\in\mathcal C_n}v_n(z)\Bigr)\ge\mathbb E(v_n)-D\ln(n+1)^{1/2}n^{-1/2},\qquad \mathbb E\Bigl(\max_{z\in\mathcal C_n}v_n(z)\Bigr)\le\mathbb E(v_n)+D\ln(n+1)^{1/2}n^{-1/2}.$$
--
--   Every state reached in the first $n+1$ stages of a play from $0$ lies in $\mathcal C_n$, so this bounds what Player 1 (resp. Player 2) can lose by having to restart an $n$-stage game from an unknown state of the cube. It follows from (3.2), stationarity and a union bound over the $(2n\|q\|_\infty+1)^d$ sites of the cube.
--
--   **Formalization Note** The min and max are `Finset.inf'`/`Finset.sup'` over the (nonempty) cube; $\mathbb E(v_n)=\int v_n(0)\,d\mathbb P$.
--
--   Differences from the source:
--   - generalization: 𝒞 := [0..n‖q‖_∞]^d (p.4) → the symmetric cube [−n‖q‖_∞..n‖q‖_∞]^d (`cube q n`); reason: the printed cube is contained in the symmetric one, so a lower bound on the min (resp. upper bound on the max) over the symmetric cube implies the same bound over the printed cube; the symmetric cube is also the one p.5 counts, |𝒞| = (2n‖q‖_∞+1)^d, and the one the next step needs (see value_add_ge_concat)
--   - generalization: the min bound (Player 1's side) → the min bound and the max bound; reason: the max bound is Player 2's side, used when the paper switches the players' roles (p.6); the min clause is the printed statement
--   - generalization: percolation game with an ergodic measure-preserving ℤ^d-action τ, τ-stationary g, and i.i.d. site vectors (Definition 2.2) → IsIID g μ: each g(z,i,j) measurable, site vectors mutually independent and identically distributed; no τ; reason: i.i.d. site vectors have a translation-invariant law, which is all the proof uses; every i.i.d. percolation game of the paper satisfies IsIID
--   - reading: g uniformly bounded (p.3) → ∃ M, |g ω z i j| ≤ M for all ω, z, i, j; reason: the proof uses ‖g‖_∞ as a deterministic constant, so the bound is uniform in ω
--   - encoding: E(v_n) := E(v_n(0)); P(event) → Bochner integral ∫ v_n(0) dμ; the measure μ of the set (outer measure if it were not measurable); reason: v_n(0) is bounded and measurable (identDistrib_value), so the integral is the expectation; the outer measure is at least the probability
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
--   - reading: ln(n + 1)^{1/2} → (ln(n + 1))^{1/2}, the definition `rate`; reason: p.5 needs this parse: λ_n = 2√2 ln(2n‖q‖_∞+1)^{1/2}(d+1)‖g‖_∞ n^{−1/2} makes λ_n²n/(8‖g‖²_∞) a multiple of ln(2n‖q‖_∞+1); for n ≥ 1 it is at most a constant times ln(n+1), so this is the stronger of the two parses
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, display after "Hence, there exists D > 0", p.6

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- The expected minimum (and maximum) of `v_n` over the cube. In an i.i.d., oriented, uniformly
bounded percolation game there is `D > 0` such that for all `n ≥ 1`,
`𝔼(min_{z ∈ 𝒞_n} v_n(z)) ≥ 𝔼(v_n) − D ln(n+1)^{1/2} n^{−1/2}` and
`𝔼(max_{z ∈ 𝒞_n} v_n(z)) ≤ 𝔼(v_n) + D ln(n+1)^{1/2} n^{−1/2}`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, display after "Hence, there exists D > 0", p.6.

**Formalization Note.** `𝒞_n = [−n‖q‖_∞ .. n‖q‖_∞]^d` is the symmetric cube (printed
`[0..n‖q‖_∞]^d`; the paper counts `(2n‖q‖_∞ + 1)^d` points). The max clause is Player 2's
counterpart, used by "Switching Players 1 and 2's roles" (p.6). -/
theorem expect_min_cube_ge {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : I → J → Site d) (g : Ω → Site d → I → J → ℝ) (hiid : IsIID g μ)
    (hbdd : ∃ M : ℝ, ∀ ω z i j, |g ω z i j| ≤ M) (hq : Oriented q) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      (∫ ω', value q (g ω') n 0 ∂μ) - D * rate n ≤ (∫ ω, cubeMin q (g ω) n ∂μ) ∧
      (∫ ω, cubeMax q (g ω) n ∂μ) ≤ (∫ ω', value q (g ω') n 0 ∂μ) + D * rate n := by sorry

end PercolationGames
