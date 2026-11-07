-- Prove2me | Theorems.Thm_SteinerNav_lemma_4_1
-- name    : SteinerNav.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:41.627612+00:00
-- url     : https://prove2.me/theorems/ac5316ec-e6ba-4e1e-8664-aa6f1f19380b
-- title:
--   Lemma 4.1 — one random point at radius $r_0\sqrt{2\varepsilon}$ covers a target at distance in $[r_0,2r_0]$ with dimension-free probability
-- statement:
--   Let $\alpha=1+1/d$ and $\varepsilon=1-1/\alpha^2=(2d+1)/(d+1)^2$. There is an absolute constant $c_0>0$ with the following property. Let $d\ge1$, let $s,t\in\mathbb R^d$ be distinct, and let $r_0>0$ with $r_0\le\|s-t\|\le 2r_0$. If $u$ is a uniformly random unit vector in $\mathbb R^d$, then the sampled point $v=s+r_0\sqrt{2\varepsilon}\,u$ satisfies
--   $$\Pr\Big[\|v-t\|<\frac{\|s-t\|}{\alpha}\Big]\ \ge\ c_0 .$$
--
--   The constant does not depend on $d$, $s$, $t$ or $r_0$. This is the geometric engine of the construction: $O(\log n)$ samples per distance scale cover every target at that scale with high probability.
--
--   **Formalization Note** $c_0$ is chosen before $d$. "Uniformly random unit vector" is the published law `uniformSphere d`, and the probability is the measure of the set of good $u$.
--
--   Differences from the source: none.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), Lemma 4.1, p.7

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_SteinerNav_annularCandidates

namespace SteinerNav

open RegretBandits.Nonlinear

/-- Lemma 4.1: a dimension-free constant `c₀ > 0` such that, for `α = 1 + 1/d`, `ε = 1 − 1/α²`, distinct
`s, t` and `r₀ > 0` with `r₀ ≤ ‖s − t‖ ≤ 2 r₀`, the point `v = s + r₀ √(2ε) u` for a uniformly random unit
vector `u` satisfies `‖v − t‖ < ‖s − t‖/α` with probability at least `c₀` (Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), Lemma 4.1, p.7).

**Formalization Note** `c₀` is chosen before `d`, `s`, `t`, `r₀`. -/
theorem lemma_4_1 : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (s t : Pt d) (r₀ : ℝ), s ≠ t → 0 < r₀ →
    r₀ ≤ dist s t → dist s t ≤ 2 * r₀ →
    ENNReal.ofReal c₀ ≤ uniformSphere d {u : Pt d |
      Covers (1 + 1 / (d : ℝ)) s (s + (r₀ * Real.sqrt (2 * samplingEps (1 + 1 / (d : ℝ)))) • u) t} := by sorry

end SteinerNav
