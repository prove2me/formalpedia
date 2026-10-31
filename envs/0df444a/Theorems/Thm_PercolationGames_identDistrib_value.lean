-- Prove2me | Theorems.Thm_PercolationGames_identDistrib_value
-- name    : PercolationGames.identDistrib_value
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:24:29.573508+00:00
-- url     : https://prove2.me/theorems/0a407225-a02d-4987-abd1-927e3a0a7610
-- title:
--   p.5 — stationarity: $v_n(z)$ and $v_n(0)$ have the same distribution
-- statement:
--   Let $g$ be an i.i.d. random payoff field on a probability space $(\Omega,\mathbb P)$. For every $n$ and every $z\in\mathbb Z^d$, the random variables
--
--   $$\omega\mapsto v_n^\omega(z)\qquad\text{and}\qquad\omega\mapsto v_n^\omega(0)$$
--
--   are (almost everywhere) measurable and have the same distribution.
--
--   In particular $\mathbb E(v_n(z))$ does not depend on $z$, which is why the paper writes $\mathbb E(v_n)$ for $\mathbb E(v_n(0))$ ("By the stationarity assumption, the expectation of $v_n(z)$ is independent of $z$", p.5). The union bound over the cube and the final step of the proof of Theorem 2.3 use this.
--
--   **Formalization Note** Identical distribution is Mathlib's `IdentDistrib`, which includes almost-everywhere measurability of both variables.
--
--   Differences from the source:
--   - generalization: percolation game with an ergodic measure-preserving ℤ^d-action τ, τ-stationary g, and i.i.d. site vectors (Definition 2.2) → IsIID g μ: each g(z,i,j) measurable, site vectors mutually independent and identically distributed; no τ; reason: i.i.d. site vectors have a translation-invariant law, which is all the proof uses; every i.i.d. percolation game of the paper satisfies IsIID
--   - generalization: the setting of §3.1: an oriented, uniformly bounded game, n ≥ 1 → no orientation, no bound, every n; reason: equality in law needs only the i.i.d. sites; the statement specializes to the paper's setting
--   - encoding: I and J finite sets → I, J finite and nonempty ([Fintype] [Nonempty]); reason: the max over Σ and the min over T are undefined for empty action sets; only that case is excluded
--   - encoding: ℤ^d; strategies σ_m, τ_m (m ≥ 1) on (ℤ^d × I × J)^{m−1}; max/min in the value → Fin d → ℤ; strategies indexed from m = 0 with Fin m-indexed histories; ⨆/⨅ in `value`; reason: same objects; the families are bounded for every payoff (finitely many reachable histories) and the value is attained (value_eq_minmax)
-- source:
--   Garnier–Ziliotto, Percolation games, arXiv:2110.12227v2, §3.1, p.5 ("Using the union bound, and then the fact that variables v_n(z) and v_n(0) have the same distribution by stationarity"; "By the stationarity assumption, the expectation of v_n(z) is independent of z")

import Mathlib
import Definitions.Def_PercolationGames_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace PercolationGames

/-- Stationarity of the value: under the i.i.d. assumption, `v_n(z)` and `v_n(0)` have the same
distribution, for every `n` and every `z ∈ ℤ^d`. In particular `v_n(z)` is (a.e.) measurable and
`𝔼(v_n(z))` does not depend on `z`.

Source: Garnier–Ziliotto, *Percolation games*, arXiv:2110.12227v2, §3.1, p.5 ("the fact that variables `v_n(z)` and `v_n(0)` have the same
distribution by stationarity"; "the expectation of `v_n(z)` is independent of `z`").

**Formalization Note.** Derived from Definition 2.2 (i.i.d. site vectors) alone; the ergodic
shift `τ` of the paper is not assumed. Neither orientation nor boundedness is needed. -/
theorem identDistrib_value {d : ℕ} {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : I → J → Site d) (g : Ω → Site d → I → J → ℝ) (hiid : IsIID g μ)
    (n : ℕ) (z : Site d) :
    IdentDistrib (fun ω => value q (g ω) n z) (fun ω => value q (g ω) n 0) μ μ := by sorry

end PercolationGames
