-- Prove2me | Theorems.Thm_StableVotingDistortion_eq_29
-- name    : StableVotingDistortion.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:33.762225+00:00
-- url     : https://prove2.me/theorems/ecf1e914-aaa8-4a4a-a77e-f741c63f9701
-- title:
--   Equations (28)⇒(29) — the per-threshold bounds integrate to $\lambda R_v$
-- statement:
--   Let $D$ be a lottery and $\rho:C\to\mathbb R_{\ge0}$ with $\rho(a^\star)=0$. Let $W:[0,1]\to\mathbb R_{\ge0}$ be nondecreasing, $v$ a voter, and $\tilde q_v$ integrable on $(0,\infty)$ such that for every $t\ge0$,
--   $$\tilde q_v(t)\le\lambda-W(q_v(t)),\qquad \tilde q_v(t)\le W(z)-W(q_v(t))\ \text{ if }z_v(t)\le z\le s_v.$$
--   Then
--   $$\int_0^\infty\tilde q_v(t)\,dt\le\lambda R_v.$$
--
--   Differences from the source:
--   - generalization: §6.3.1's setting: $D$ a $g_\phi$-stable lottery, $\phi$ satisfying (26), $\lambda\in(0,1)$ → any lottery `D ∈ stdSimplex ℝ C`, no $\phi$, and any real `lam`; reason: the telescoping argument of p.28 uses only (27), (28) and $W\ge0$; the page's instance satisfies these hypotheses, so the statement specializes to the page's
--   - encoding: $\tilde q_v$ with $\int_0^\infty\tilde q_v$ → the hypothesis `IntegrableOn qT (Set.Ioi 0)`; reason: $\tilde q_v$ is arbitrary here and a Bochner integral of a non-integrable function is $0$; the $\tilde q_v$ of (32) is piecewise constant and satisfies it
--   - encoding: $W:[0,1]\to\mathbb R_{\ge0}$ → `W : ℝ → ℝ`, monotone and nonnegative on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (28), (29), pp.27–28

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_rhoV
import Definitions.Def_StableVotingDistortion_slices

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Equations (28) ⇒ (29).** Let `W : [0, 1] → ℝ≥0` be nondecreasing, `v` a voter, and `q̃_v` integrable on
`(0, ∞)` with, for every `t ≥ 0`, `q̃_v(t) ≤ λ − W(q_v(t))` and `q̃_v(t) ≤ W(z) − W(q_v(t))` whenever
`z_v(t) ≤ z ≤ s_v`. Then `∫_0^∞ q̃_v(t) dt ≤ λ R_v`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equations (28), (29), pp.27–28: "find a nondecreasing function W : [0, 1] → R≥0 such that for
every v and t ≥ 0, q̃_v(t) ≤ λ − W(q_v(t)), q̃_v(t) ≤ W(z) − W(q_v(t)) if z_v(t) ≤ z ≤ s_v. (28)" and "and so
∫_0^∞ q̃_v(t) dt ≤ λR_v. (29)"

**Formalization Note.** `q̃_v` is arbitrary here, so its integrability is a hypothesis: a Bochner integral
of a non-integrable function would be `0`. The `q̃_v` of (32) is piecewise constant and satisfies it. -/
theorem eq_29 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {D ρ : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (hρ : ∀ c, 0 ≤ ρ c) {aStar : C} (hstar : ρ aStar = 0)
    (lam : ℝ) {W : ℝ → ℝ} (hWmono : MonotoneOn W (Set.Icc 0 1))
    (hWnonneg : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 ≤ W z) (v : V) {qT : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn qT (Set.Ioi 0))
    (h28a : ∀ t, 0 ≤ t → qT t ≤ lam - W (qv E D ρ v t))
    (h28b : ∀ t, 0 ≤ t → ∀ z, zv E D ρ v t ≤ z → z ≤ sv E D aStar v →
      qT t ≤ W z - W (qv E D ρ v t)) :
    ∫ t in Set.Ioi (0 : ℝ), qT t ≤ lam * Rv E ρ v := by sorry

end StableVotingDistortion
