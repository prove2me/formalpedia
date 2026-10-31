-- Prove2me | Theorems.Thm_PercolationGames_concentration
-- name    : PercolationGames.concentration
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:27.398203+00:00
-- url     : https://prove2.me/theorems/96e59306-6174-4c42-988f-850afeb4a990
-- title:
--   (3.2), p.5 — concentration $\mathbb P(|v_n(0)-\mathbb E(v_n)|\ge\lambda)\le2\exp(-\lambda^2n/(8CM^2))$ (corrected: factor 2 and the constant $C$ in the exponent)
-- statement:
--   Let $q$ be an oriented transition function. There is a constant $C>0$, depending on $q$ but not on the payoff field, $n$ or $\lambda$, such that in every i.i.d. percolation game on $q$ with $|g_\omega(z,i,j)|\le M$ for all $\omega,z,i,j$, and for all $n\ge1$ and $\lambda\ge0$,
--
--   $$\mathbb P\bigl(|v_n(0)-\mathbb E(v_n)|\ge\lambda\bigr)\le 2\exp\Bigl(-\frac{\lambda^2n}{8CM^2}\Bigr).$$
--
--   This is the concentration half of the proof of Theorem 2.3: Azuma's inequality applied to the martingale $W_r=\mathbb E(v_n(0)\mid\mathcal F_r)$ over the $Cn$ hyperplanes meeting the cube, with increments bounded by (3.1).
--
--   **Formalization Note** The printed bound $\exp(-\lambda^2n/(8\|g\|_\infty^2))$ is false (see below): two-sided Azuma contributes the factor $2$, and the number $Cn$ of increments puts $C$ in the exponent. $\mathbb E(v_n)$ is the Bochner integral of $v_n(0)$; the bound is on the measure of the set $\{\omega:\lambda\le|v_n^\omega(0)-\mathbb E(v_n)|\}$.
--
--   Differences from the source:
--   - correction: P(|v_n(0) − E(v_n)| ≥ λ) ≤ exp(−λ²n/(8‖g‖²_∞)) for all λ ≥ 0 → ∃ C > 0 depending on q only, for every i.i.d. field with |g| ≤ M, ∀ n ≥ 1, ∀ λ ≥ 0, P(…) ≤ 2 exp(−λ²n/(8CM²)); reason: the printed bound is false: d = 1, I = J = {∗}, q = 1, u = 1, i.i.d. Rademacher payoffs (stationary, ergodic, i.i.d., ‖g‖_∞ = 1), n = 1, λ = 1 give v_1(0) = g(0,∗,∗), E(v_1) = 0 and P(|v_1(0)| ≥ 1) = 1 > exp(−1/8); Azuma over the Cn increments of (3.1) gives the corrected bound, where C is the constant of p.4, which depends on u, d and ‖q‖_∞, hence on q
--   - generalization: percolation game with an ergodic measure-preserving ℤ^d-action τ, τ-stationary g, and i.i.d. site vectors (Definition 2.2) → IsIID g μ: each g(z,i,j) measurable, site vectors mutually independent and identically distributed; no τ; reason: i.i.d. site vectors have a translation-invariant law, which is all the proof uses; every i.i.d. percolation game of the paper satisfies IsIID
--   - generalization: ‖g‖_∞ → any M with |g ω z i j| ≤ M for all ω, z, i, j; reason: ‖g‖_∞ is such an M; the statement specializes to it
--   - encoding: division by 8‖g‖²_∞, undefined at ‖g‖_∞ = 0 → Lean division, so at M = 0 the exponent is 0 and the bound is the trivial 2; reason: the only instance is g = 0, where v_n(0) = E(v_n) = 0 and the printed formula has no meaning
--   - encoding: E(v_n) := E(v_n(0)); P(event) → Bochner integral ∫ v_n(0) dμ; the measure μ of the set (outer measure if it were not measurable); reason: v_n(0) is bounded and measurable (identDistrib_value), so the integral is the expectation; the outer measure is at least the probability
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, display (3.2), p.5

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- Display (3.2), corrected: concentration of `v_n(0)`. For an oriented transition `q` there is
a constant `C > 0`, depending on `q` only, such that in every i.i.d. game on `q` with `|g| ≤ M`,
for all `n ≥ 1` and `t ≥ 0`, `ℙ(|v_n(0) − 𝔼(v_n)| ≥ t) ≤ 2 exp(−t² n / (8 C M²))`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, display (3.2), p.5.

**Formalization Note.** Corrected: the printed bound `exp(−t² n / (8‖g‖²_∞))` is false (with
`d = 1`, one action each, `q = 1`, Rademacher payoffs, `n = 1`, `t = 1` the probability is `1`).
Azuma over the `Cn` hyperplanes meeting the cube restores the factor `2` and the number `C` of
hyperplanes per stage, the constant `C` of p.4; it depends on `u`, `d` and `‖q‖_∞`, hence on `q`,
so it is quantified after `q` and before the payoff field. `M` is any uniform bound on `|g|` (the
paper's `‖g‖_∞` is the least one); at `M = 0` Lean's division by zero makes the bound the trivial
`2`. `𝔼(v_n) = ∫ v_n(0) dμ`. The probability is the measure of the set (its outer measure if it
were not measurable). -/
theorem concentration {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (q : I → J → Site d) (hq : Oriented q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : Ω → Site d → I → J → ℝ) (_hiid : IsIID g μ)
      (M : ℝ) (_hM : ∀ ω z i j, |g ω z i j| ≤ M) (n : ℕ) (_hn : 1 ≤ n) (t : ℝ) (_ht : 0 ≤ t),
      μ {ω | t ≤ |value q (g ω) n 0 - (∫ ω', value q (g ω') n 0 ∂μ)|} ≤
        ENNReal.ofReal (2 * Real.exp (-(t ^ 2 * n / (8 * C * M ^ 2)))) := by sorry

end PercolationGames
