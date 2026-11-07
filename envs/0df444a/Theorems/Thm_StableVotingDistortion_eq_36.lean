-- Prove2me | Theorems.Thm_StableVotingDistortion_eq_36
-- name    : StableVotingDistortion.eq_36
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:23.067231+00:00
-- url     : https://prove2.me/theorems/3a612027-e127-4a3d-9977-c4a7e014fae6
-- title:
--   Equation (36) — the block-score bounds $k_v(t)\le\delta_p(q)$ and $k_v(t)\le K_p(q,z)$
-- statement:
--   Let $\lambda\in(0,1)$, $\phi$ satisfy (26), $D$ be a lottery, $\rho\ge0$ with $\rho(a^\star)=0$, $t\ge0$ and $v$ a voter. Write $p=p_t$ and $q=q_v(t)$. Then
--   $$k_v(t)\le\delta_p(q)=J(1-p+q)-J(q),$$
--   and for every $z$ with $z_v(t)\le z\le1$,
--   $$k_v(t)\le K_p(q,z)=J(z-p+q)-J(z)-J(q).$$
--
--   Differences from the source:
--   - generalization: §6.3.1's setting: $D$ a $g_\phi$-stable lottery → any lottery `D ∈ stdSimplex ℝ C`; reason: (36) bounds the score of a block on one rank line using only (26); a $g_\phi$-stable lottery is a lottery, so the statement specializes to the page's
--   - encoding: $z\ge z_v(t)$ → $z_v(t)\le z\le1$; reason: $z$ is a point of the rank line $[0,1]$, on which $J$ is defined
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equation (36), p.29

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_slices

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Equation (36).** Under (26), for any lottery, `ρ ≥ 0` with `ρ(a⋆) = 0`, `t ≥ 0` and a voter `v`, with
`p = p_t` and `q = q_v(t)`: `k_v(t) ≤ δ_p(q)`, and `k_v(t) ≤ K_p(q, z)` for every `z` with `z_v(t) ≤ z ≤ 1`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equation (36), p.29: "k_v(t) ≤ δ_p(q) = J(1 − p + q) − J(q), k_v(t) ≤ K_p(q, z) =
J(z − p + q) − J(z) − J(q). (36)"; the page's sentence before it: "in terms of p = p_t, q = q_v(t), and
z ≥ z_v(t)". -/
theorem eq_36 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    {D ρ : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (hρ : ∀ b, 0 ≤ ρ b) {aStar : C} (hstar : ρ aStar = 0)
    {t : ℝ} (ht : 0 ≤ t) (v : V) :
    kv E D ρ ϕ v t ≤ deltaP ϕ (pt D ρ t) (qv E D ρ v t) ∧
      ∀ z, zv E D ρ v t ≤ z → z ≤ 1 → kv E D ρ ϕ v t ≤ KP ϕ (pt D ρ t) (qv E D ρ v t) z := by sorry

end StableVotingDistortion
