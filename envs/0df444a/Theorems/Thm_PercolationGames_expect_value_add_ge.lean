-- Prove2me | Theorems.Thm_PercolationGames_expect_value_add_ge
-- name    : PercolationGames.expect_value_add_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:28.464065+00:00
-- url     : https://prove2.me/theorems/711fe66b-7694-4a58-afb7-17e3cfb5337a
-- title:
--   (3.3), p.6 — near-superadditivity of $n\mathbb E(v_n)$, and the symmetric bound (corrected: symmetric cube)
-- statement:
--   Consider an i.i.d., oriented percolation game with uniformly bounded payoffs. There is $D>0$ such that for all $n\ge1$ and $m\in[1..n]$,
--
--   $$\mathbb E(v_{m+n})\ge\frac m{m+n}\mathbb E(v_m)+\frac n{m+n}\mathbb E\Bigl(\min_{z\in\mathcal C_n}v_n(z)\Bigr)\ge\frac m{m+n}\mathbb E(v_m)+\frac n{m+n}\Bigl[\mathbb E(v_n)-D\ln(n+1)^{1/2}n^{-1/2}\Bigr]$$
--
--   and, switching the players' roles,
--
--   $$\mathbb E(v_{m+n})\le\frac m{m+n}\mathbb E(v_m)+\frac n{m+n}\mathbb E\Bigl(\max_{z\in\mathcal C_n}v_n(z)\Bigr)\le\frac m{m+n}\mathbb E(v_m)+\frac n{m+n}\Bigl[\mathbb E(v_n)+D\ln(n+1)^{1/2}n^{-1/2}\Bigr].$$
--
--   With $a_n=-n\mathbb E(v_n)$ the first chain says that $(a_n)$ is subadditive with the error term $f(n)=D\ln(n+1)^{1/2}n^{1/2}$, which drives the convergence of $\mathbb E(v_n)$.
--
--   **Formalization Note** $\mathbb E(v_k)=\int v_k(0)\,d\mathbb P$ and $\mathcal C_n=[-n\|q\|_\infty..n\|q\|_\infty]^d$.
--
--   Differences from the source:
--   - correction: 𝒞 := [0..n‖q‖_∞]^d (p.4) → the symmetric cube [−n‖q‖_∞..n‖q‖_∞]^d (`cube q n`); reason: with the printed cube the first inequality of (3.3) is false: d = 2, u = (−1, 0), I = {∗}, J the 10 points of {−2, −1} × {−2..2}, q(∗, j) = j, so ‖q‖_∞ = 2, i.i.d. Rademacher payoffs g(z, ∗, j) = g(z), m = n = 1; then v_1(z) = g(z), E(v_2) = ½E(min of 10 sites) = ½(−1 + 2^{−9}) < ½(−1 + 2^{−8}) = ½E(v_1) + ½E(min_{z∈[0..2]²} v_1(z)); p.5 counts |𝒞| = (2n‖q‖_∞+1)^d, which is the symmetric cube
--   - generalization: the lower chain (3.3) → the lower chain and the upper chain with the max over 𝒞_n; reason: the upper chain is the role switch of p.6; the lower chain is the printed statement
--   - generalization: percolation game with an ergodic measure-preserving ℤ^d-action τ, τ-stationary g, and i.i.d. site vectors (Definition 2.2) → IsIID g μ: each g(z,i,j) measurable, site vectors mutually independent and identically distributed; no τ; reason: i.i.d. site vectors have a translation-invariant law, which is all the proof uses; every i.i.d. percolation game of the paper satisfies IsIID
--   - reading: g uniformly bounded (p.3) → ∃ M, |g ω z i j| ≤ M for all ω, z, i, j; reason: the proof uses ‖g‖_∞ as a deterministic constant, so the bound is uniform in ω
--   - encoding: E(v_n) := E(v_n(0)); P(event) → Bochner integral ∫ v_n(0) dμ; the measure μ of the set (outer measure if it were not measurable); reason: v_n(0) is bounded and measurable (identDistrib_value), so the integral is the expectation; the outer measure is at least the probability
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
--   - reading: ln(n + 1)^{1/2} → (ln(n + 1))^{1/2}, the definition `rate`; reason: p.5 needs this parse: λ_n = 2√2 ln(2n‖q‖_∞+1)^{1/2}(d+1)‖g‖_∞ n^{−1/2} makes λ_n²n/(8‖g‖²_∞) a multiple of ln(2n‖q‖_∞+1); for n ≥ 1 it is at most a constant times ln(n+1), so this is the stronger of the two parses
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, display (3.3), p.6

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- Display (3.3) and its symmetric counterpart. In an i.i.d., oriented, uniformly bounded
percolation game there is `D > 0` such that for all `n ≥ 1` and `m ∈ [1..n]`,
`𝔼(v_{m+n}) ≥ (m/(m+n)) 𝔼(v_m) + (n/(m+n)) 𝔼(min_{z ∈ 𝒞_n} v_n(z))
  ≥ (m/(m+n)) 𝔼(v_m) + (n/(m+n)) [𝔼(v_n) − D ln(n+1)^{1/2} n^{−1/2}]` and, switching the
players' roles,
`𝔼(v_{m+n}) ≤ (m/(m+n)) 𝔼(v_m) + (n/(m+n)) 𝔼(max_{z ∈ 𝒞_n} v_n(z))
  ≤ (m/(m+n)) 𝔼(v_m) + (n/(m+n)) [𝔼(v_n) + D ln(n+1)^{1/2} n^{−1/2}]`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, display (3.3), p.6.

**Formalization Note.** `𝔼(v_k) = ∫ v_k(0) dμ`; Corrected: `𝒞_n` is the symmetric
cube; with the printed `[0..n‖q‖_∞]^d` the first inequality of (3.3) is false (a Player 2 with more
reachable sites than the printed cube has points). The second pair
of inequalities is the role switch (p.6). -/
theorem expect_value_add_ge {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : I → J → Site d) (g : Ω → Site d → I → J → ℝ) (hiid : IsIID g μ)
    (hbdd : ∃ M : ℝ, ∀ ω z i j, |g ω z i j| ≤ M) (hq : Oriented q) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m → m ≤ n →
      ((m : ℝ) / ((m : ℝ) + n) * (∫ ω', value q (g ω') m 0 ∂μ) +
            (n : ℝ) / ((m : ℝ) + n) * (∫ ω, cubeMin q (g ω) n ∂μ) ≤ (∫ ω', value q (g ω') (m + n) 0 ∂μ) ∧
        (m : ℝ) / ((m : ℝ) + n) * (∫ ω', value q (g ω') m 0 ∂μ) +
            (n : ℝ) / ((m : ℝ) + n) * ((∫ ω', value q (g ω') n 0 ∂μ) - D * rate n) ≤
          (m : ℝ) / ((m : ℝ) + n) * (∫ ω', value q (g ω') m 0 ∂μ) +
            (n : ℝ) / ((m : ℝ) + n) * (∫ ω, cubeMin q (g ω) n ∂μ)) ∧
      ((∫ ω', value q (g ω') (m + n) 0 ∂μ) ≤
          (m : ℝ) / ((m : ℝ) + n) * (∫ ω', value q (g ω') m 0 ∂μ) +
            (n : ℝ) / ((m : ℝ) + n) * (∫ ω, cubeMax q (g ω) n ∂μ) ∧
        (m : ℝ) / ((m : ℝ) + n) * (∫ ω', value q (g ω') m 0 ∂μ) +
            (n : ℝ) / ((m : ℝ) + n) * (∫ ω, cubeMax q (g ω) n ∂μ) ≤
          (m : ℝ) / ((m : ℝ) + n) * (∫ ω', value q (g ω') m 0 ∂μ) +
            (n : ℝ) / ((m : ℝ) + n) * ((∫ ω', value q (g ω') n 0 ∂μ) + D * rate n)) := by sorry

end PercolationGames
