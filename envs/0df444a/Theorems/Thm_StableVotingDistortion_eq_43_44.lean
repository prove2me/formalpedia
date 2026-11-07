-- Prove2me | Theorems.Thm_StableVotingDistortion_eq_43_44
-- name    : StableVotingDistortion.eq_43_44
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:01:40.984291+00:00
-- url     : https://prove2.me/theorems/c261b79a-45c3-4daa-8e53-1f4c9066f4f7
-- title:
--   Equations (43)–(44) — elementary bounds on $\delta_p$, $J$ and $K_p$
-- statement:
--   Let $\lambda\in(0,1)$ and let $\phi$ satisfy (26). For $0\le q\le p\le1$,
--   $$\delta_p(q)\le p-q,\qquad \delta_p(q)\le(1-p)\phi(q),\qquad J(q)\ge q\phi(q),$$
--   and for $0\le q\le p\le z\le1$,
--   $$K_p(q,z)\le-(p-q)\phi(z)-J(q).$$
--
--   Differences from the source:
--   - reading: (43), (44) with the range of $p,q$ left implicit, and $z\ge p$ → $0\le q\le p\le1$ in (43), $0\le q\le p\le z\le1$ in (44); reason: these are the ranges of (37) and (38), and they keep every printed argument in $[0,1]$
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), App. C.1, Equations (43), (44), p.43

import Mathlib
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives

set_option autoImplicit false

namespace StableVotingDistortion

/-- **Equations (43)–(44).** Under (26): for `0 ≤ q ≤ p ≤ 1`, `δ_p(q) ≤ p − q`, `δ_p(q) ≤ (1 − p) ϕ(q)` and
`J(q) ≥ q ϕ(q)`; and for `0 ≤ q ≤ p ≤ z ≤ 1`, `K_p(q, z) ≤ −(p − q) ϕ(z) − J(q)`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), App. C.1, Equations (43), (44), p.43: "δ_p(q) ≤ p − q, δ_p(q) ≤ (1 − p) ϕ(q), J(q) ≥ q ϕ(q). (43)
Similarly, for z ≥ p, since ϕ(r) ≥ ϕ(z) on [z − p + q, z], we have K_p(q, z) ≤ −(p − q) ϕ(z) − J(q). (44)"

**Formalization Note.** The page leaves the range of `p, q` implicit; these are the ranges of `(37)`, `(38)`,
and the printed arguments lie in `[0, 1]` on them. -/
theorem eq_43_44 {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ) :
    (∀ p q, 0 ≤ q → q ≤ p → p ≤ 1 →
      deltaP ϕ p q ≤ p - q ∧ deltaP ϕ p q ≤ (1 - p) * ϕ q ∧ q * ϕ q ≤ J ϕ q) ∧
      ∀ p q z, 0 ≤ q → q ≤ p → p ≤ z → z ≤ 1 → KP ϕ p q z ≤ -(p - q) * ϕ z - J ϕ q := by sorry

end StableVotingDistortion
