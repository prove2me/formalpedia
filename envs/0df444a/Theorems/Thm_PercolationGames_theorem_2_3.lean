-- Prove2me | Theorems.Thm_PercolationGames_theorem_2_3
-- name    : PercolationGames.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:44.651683+00:00
-- url     : https://prove2.me/theorems/7394f1ed-ca16-4af3-8496-3c59a3e99872
-- title:
--   Theorem 2.3, p.4 — in i.i.d. oriented percolation games $v_n(z)\to v_\infty$ a.s., with deviations $\mathbb P(|v_n(z)-v_\infty|\ge\lambda+A\ln(n+1)^{1/2}n^{-1/2})\le e^{-B\lambda^2n}$
-- statement:
--   Consider a percolation game with finite action sets $I,J$, transition $q:I\times J\to\mathbb Z^d$ and uniformly bounded random payoffs $g$ on a probability space $(\Omega,\mathbb P)$, and assume that it is **i.i.d.** (Definition 2.2) and **oriented** (Definition 2.1). Write $v_n(z)$ for the random variable $\omega\mapsto v_n^\omega(z)$, the value of the $n$-stage game from $z$. Then there is a constant $v_\infty\in\mathbb R$ such that:
--
--   1. for every $z\in\mathbb Z^d$, $v_n(z)\to v_\infty$ $\mathbb P$-almost surely as $n\to\infty$;
--   2. there are $A,B>0$ such that for all $n\ge1$, all $z\in\mathbb Z^d$ and all $\lambda\ge0$,
--   $$\mathbb P\Bigl(|v_n(z)-v_\infty|\ge\lambda+A\ln(n+1)^{1/2}n^{-1/2}\Bigr)\le\exp\bigl(-B\lambda^2n\bigr);\tag{2.1}$$
--   3. there is $A'>0$ such that $|\mathbb E(v_n(z))-v_\infty|\le A'\ln(n+1)^{1/2}n^{-1/2}$ for all $n\ge1$ and $z\in\mathbb Z^d$; in particular $\mathbb E(v_n)$ converges to $v_\infty$ at rate $O(\ln(n)n^{-1/2})$.
--
--   This is the paper's main result: in a random environment that is i.i.d. across sites, the long zero-sum percolation game has a deterministic limit value, with sub-Gaussian fluctuations at scale $n^{-1/2}$ up to a logarithmic factor. Theorem 2.4 of the paper shows that orientation alone, without the i.i.d. assumption, does not suffice.
--
--   **Formalization Note** $\mathbb Z^d$ is `Fin d → ℤ`; $v_n^\omega(z)$ is the max–min over pure history-dependent strategies, with Player 2 observing Player 1's current action. The i.i.d. hypothesis is measurability of every $g(z,i,j)$ plus mutual independence and identical distribution of the site vectors; the paper's ergodic shift is not assumed. $\mathbb P(\cdot)$ is the measure of the set and $\mathbb E$ the Bochner integral.
--
--   Differences from the source:
--   - generalization: percolation game with an ergodic measure-preserving ℤ^d-action τ, τ-stationary g, and i.i.d. site vectors (Definition 2.2) → IsIID g μ: each g(z,i,j) measurable, site vectors mutually independent and identically distributed; no τ; reason: i.i.d. site vectors have a translation-invariant law, which is all the proof uses; every i.i.d. percolation game of the paper satisfies IsIID
--   - generalization: In particular, E(v_n) converges to v_∞ at a rate O(ln(n) n^{−1/2}) → ∃ A′ > 0, ∀ n ≥ 1, ∀ z, |E(v_n(z)) − v_∞| ≤ A′ ln(n+1)^{1/2} n^{−1/2}; reason: it is the bound the proof establishes (p.6) and implies the O-statement, since ln(n+1)^{1/2} ≤ 2 ln n for n ≥ 3; by stationarity E(v_n(z)) = E(v_n)
--   - reading: g uniformly bounded (p.3) → ∃ M, |g ω z i j| ≤ M for all ω, z, i, j; reason: the proof uses ‖g‖_∞ as a deterministic constant, so the bound is uniform in ω
--   - encoding: E(v_n) := E(v_n(0)); P(event) → Bochner integral ∫ v_n(0) dμ; the measure μ of the set (outer measure if it were not measurable); reason: v_n(0) is bounded and measurable (identDistrib_value), so the integral is the expectation; the outer measure is at least the probability
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
--   - reading: ln(n + 1)^{1/2} → (ln(n + 1))^{1/2}, the definition `rate`; reason: p.5 needs this parse: λ_n = 2√2 ln(2n‖q‖_∞+1)^{1/2}(d+1)‖g‖_∞ n^{−1/2} makes λ_n²n/(8‖g‖²_∞) a multiple of ln(2n‖q‖_∞+1); for n ≥ 1 it is at most a constant times ln(n+1), so this is the stronger of the two parses
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, Theorem 2.3 and display (2.1), p.4; proof §3.1, pp.4–6

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- Theorem 2.3. Consider a percolation game that is i.i.d. and oriented, with uniformly bounded
payoffs. There is a constant `v_∞ ∈ ℝ` such that

1. for all `z ∈ ℤ^d`, `v_n(z) → v_∞` almost surely as `n → ∞`;
2. there are `A, B > 0` such that for all `n ≥ 1`, `z ∈ ℤ^d` and `t ≥ 0`,
   `ℙ(|v_n(z) − v_∞| ≥ t + A ln(n+1)^{1/2} n^{−1/2}) ≤ exp(−B t² n)` (2.1);
3. there is `A' > 0` with `|𝔼(v_n(z)) − v_∞| ≤ A' ln(n+1)^{1/2} n^{−1/2}` for all `n ≥ 1` and
   `z ∈ ℤ^d` (the rate `O(ln(n) n^{−1/2})` of `𝔼(v_n)`).

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, Theorem 2.3 and display (2.1), p.4; proof §3.1, pp.4–6.

**Formalization Note.** The game is given by finite nonempty action sets `I`, `J`, a transition
`q : I → J → ℤ^d` (`ℤ^d` as `Fin d → ℤ`) and a payoff field `g` on a probability space. The
paper's ergodic shift `τ` and stationarity are not assumed: i.i.d. site vectors (Definition 2.2)
plus a uniform bound are the hypotheses, which every game of the paper satisfies. Clause 3 is
the explicit bound the proof gives, for every `n ≥ 1`, in place of the `O`-statement.
`v_n(z)(ω) = value q (g ω) n z` is the max-min over pure history-dependent strategies.
Probabilities are measures of sets (outer measure if a set were not measurable). -/
theorem theorem_2_3 {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : I → J → Site d) (g : Ω → Site d → I → J → ℝ) (hiid : IsIID g μ)
    (hbdd : ∃ M : ℝ, ∀ ω z i j, |g ω z i j| ≤ M) (hq : Oriented q) :
    ∃ v : ℝ,
      (∀ z : Site d, ∀ᵐ ω ∂μ,
        Tendsto (fun n : ℕ => value q (g ω) n z) atTop (𝓝 v)) ∧
      (∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : Site d, ∀ t : ℝ, 0 ≤ t →
        μ {ω | t + A * rate n ≤
            |value q (g ω) n z - v|} ≤
          ENNReal.ofReal (Real.exp (-(B * t ^ 2 * n)))) ∧
      (∃ A' : ℝ, 0 < A' ∧ ∀ n : ℕ, 1 ≤ n → ∀ z : Site d,
        |(∫ ω, value q (g ω) n z ∂μ) - v| ≤ A' * rate n) := by sorry

end PercolationGames
