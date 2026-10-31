-- Prove2me | Theorems.Thm_PercolationGames_expect_value_dyadic
-- name    : PercolationGames.expect_value_dyadic
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:42.335009+00:00
-- url     : https://prove2.me/theorems/10f3f540-b9da-4b54-88a9-0f24b0646268
-- title:
--   p.6 — dyadic iteration: $|\mathbb E(v_{2^\ell n})-\mathbb E(v_n)|\le A\ln(n+1)^{1/2}n^{-1/2}$ for all $\ell,n\ge1$
-- statement:
--   Consider an i.i.d., oriented percolation game with uniformly bounded payoffs. There are $D,A>0$ such that for all $\ell\ge1$ and $n\ge1$,
--
--   $$\mathbb E(v_{2^\ell n})\ge\mathbb E(v_n)-D\sum_{k=0}^{\ell-1}\ln(2^kn+1)^{1/2}2^{-k/2}n^{-1/2}\ge\mathbb E(v_n)-A\ln(n+1)^{1/2}n^{-1/2}$$
--
--   and, switching the players' roles,
--
--   $$\mathbb E(v_{2^\ell n})\le\mathbb E(v_n)+D\sum_{k=0}^{\ell-1}\ln(2^kn+1)^{1/2}2^{-k/2}n^{-1/2}\le\mathbb E(v_n)+A\ln(n+1)^{1/2}n^{-1/2}.$$
--
--   The first inequality of each chain is (3.3) with $m=n$ iterated $\ell$ times; the second bounds the series. Letting $\ell\to\infty$ gives the rate of convergence of $\mathbb E(v_n)$.
--
--   **Formalization Note** $\mathbb E(v_k)=\int v_k(0)\,d\mathbb P$, and the $k$-th term of the sum is `rate (2 ^ k * n)`. $D$ and $A$ may depend on the game but not on $\ell$ or $n$.
--
--   Differences from the source:
--   - reading: where A is a universal constant → ∃ A > 0 depending on the game, uniform in ℓ and n; reason: A is built from D, which depends on the game; scaling the payoffs by K scales E(v_{2^ℓ n}) − E(v_n) by K, so A cannot be independent of the game
--   - generalization: the lower chain → the lower and the upper chain; reason: the upper chain is the role switch of p.6; the lower chain is the printed statement
--   - generalization: percolation game with an ergodic measure-preserving ℤ^d-action τ, τ-stationary g, and i.i.d. site vectors (Definition 2.2) → IsIID g μ: each g(z,i,j) measurable, site vectors mutually independent and identically distributed; no τ; reason: i.i.d. site vectors have a translation-invariant law, which is all the proof uses; every i.i.d. percolation game of the paper satisfies IsIID
--   - reading: g uniformly bounded (p.3) → ∃ M, |g ω z i j| ≤ M for all ω, z, i, j; reason: the proof uses ‖g‖_∞ as a deterministic constant, so the bound is uniform in ω
--   - encoding: E(v_n) := E(v_n(0)); P(event) → Bochner integral ∫ v_n(0) dμ; the measure μ of the set (outer measure if it were not measurable); reason: v_n(0) is bounded and measurable (identDistrib_value), so the integral is the expectation; the outer measure is at least the probability
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
--   - encoding: D of (3.3) → ∃ D > 0 in this item, not linked to the D of expect_value_add_ge; reason: each item has its own existential constant; D is the constant of (3.3) up to the factor from m = n, and the proof supplies it from there
--   - reading: ln(n + 1)^{1/2} → (ln(n + 1))^{1/2}, the definition `rate`; reason: p.5 needs this parse: λ_n = 2√2 ln(2n‖q‖_∞+1)^{1/2}(d+1)‖g‖_∞ n^{−1/2} makes λ_n²n/(8‖g‖²_∞) a multiple of ln(2n‖q‖_∞+1); for n ≥ 1 it is at most a constant times ln(n+1), so this is the stronger of the two parses
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, display after "inequality (3.3) gives by induction", p.6

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- Dyadic iteration of (3.3). In an i.i.d., oriented, uniformly bounded percolation game there
are `D, A > 0` such that for all `ℓ ≥ 1` and `n ≥ 1`,
`𝔼(v_{2^ℓ n}) ≥ 𝔼(v_n) − D ∑_{k=0}^{ℓ−1} ln(2^k n + 1)^{1/2} 2^{−k/2} n^{−1/2}
  ≥ 𝔼(v_n) − A ln(n+1)^{1/2} n^{−1/2}`, and, switching the players' roles,
`𝔼(v_{2^ℓ n}) ≤ 𝔼(v_n) + D ∑_{k=0}^{ℓ−1} ln(2^k n + 1)^{1/2} 2^{−k/2} n^{−1/2}
  ≤ 𝔼(v_n) + A ln(n+1)^{1/2} n^{−1/2}`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, display after "inequality (3.3) gives by induction", p.6.

**Formalization Note.** `𝔼(v_k) = ∫ v_k(0) dμ`. The `k`-th term of the printed sum,
`ln(2^k n + 1)^{1/2} 2^{−k/2} n^{−1/2}`, is `rate (2 ^ k * n)`. `A` depends on the game (the
paper's "universal constant" depends on `D`) but not on `ℓ` or `n`. The upper chain is the role
switch. -/
theorem expect_value_dyadic {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : I → J → Site d) (g : Ω → Site d → I → J → ℝ) (hiid : IsIID g μ)
    (hbdd : ∃ M : ℝ, ∀ ω z i j, |g ω z i j| ≤ M) (hq : Oriented q) :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ n : ℕ, 1 ≤ n →
      ((∫ ω', value q (g ω') n 0 ∂μ) - D * ∑ k ∈ Finset.range ℓ, rate (2 ^ k * n) ≤
          (∫ ω', value q (g ω') (2 ^ ℓ * n) 0 ∂μ) ∧
        (∫ ω', value q (g ω') n 0 ∂μ) - A * rate n ≤
          (∫ ω', value q (g ω') n 0 ∂μ) - D * ∑ k ∈ Finset.range ℓ, rate (2 ^ k * n)) ∧
      ((∫ ω', value q (g ω') (2 ^ ℓ * n) 0 ∂μ) ≤
          (∫ ω', value q (g ω') n 0 ∂μ) + D * ∑ k ∈ Finset.range ℓ, rate (2 ^ k * n) ∧
        (∫ ω', value q (g ω') n 0 ∂μ) + D * ∑ k ∈ Finset.range ℓ, rate (2 ^ k * n) ≤
          (∫ ω', value q (g ω') n 0 ∂μ) + A * rate n) := by sorry

end PercolationGames
