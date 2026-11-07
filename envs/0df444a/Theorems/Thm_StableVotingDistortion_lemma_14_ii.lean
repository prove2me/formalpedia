-- Prove2me | Theorems.Thm_StableVotingDistortion_lemma_14_ii
-- name    : StableVotingDistortion.lemma_14_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:34.96916+00:00
-- url     : https://prove2.me/theorems/90e7a418-5cc9-4b59-a7ff-c2510de797c1
-- title:
--   Lemma 14(ii) — large masses: (37), (38) for $p\in[p_1,1)$ with $\beta(p)=p/J(p)$
-- statement:
--   Let $\lambda\in(0,1)$, let $\phi$ satisfy (26) with $\phi(r)+r$ nonincreasing on $[\lambda,1]$, and let $\lambda<p_1<1$. Suppose $\phi(r)=\lambda-r$ on an interval $[r_-,z_+]\subseteq[0,1]$ with $r_-<\lambda$ and $\lambda+(1-p_1)\le z_+$, that $\phi$ is concave on $[\lambda,1]$, and that for constants $0<m_0<1\le M$,
--   $$\phi(r)-\phi(s)\le m_0(s-r)\ \ (0\le r<s\le r_-),\qquad \phi(r)-\phi(s)\le M(s-r)\ \ (p_1\le r<s\le1).$$
--   If, for every $p\in[p_1,1)$, (25) holds and
--   $$m_0p(1-p)\le J(p)\le p(1-p),\qquad p(1-(M+1)(1-p))\ge(M-1)J(p),$$
--   then (37) and (38) hold for every $p\in[p_1,1)$ with $\beta(p)=p/J(p)$ and $c(p,x)=(\lambda-x-\beta(p)(1-p)\phi(x))_+$.
--
--   Differences from the source:
--   - reading: "$\phi$ satisfy the hypotheses of Lemma 8", and $0<p_0<\lambda<p_1<1$ → the hypotheses on $\phi$ only, and $\lambda<p_1<1$; reason: $\beta$ and $c$ are what the lemma produces, and $p_0$ plays no part in (ii)
--   - encoding: an interval $[r_-,z_+]$ on which $\phi(r)=\lambda-r$ → with `0 ≤ rm` and `zp ≤ 1`; reason: $\phi$ is a function on $[0,1]$, so the interval lies there
--   - encoding: $\phi:[0,1]\to\mathbb R$ → a function `ℝ → ℝ` constrained only on `[0, 1]`; reason: Lean functions are total; every printed argument lies in $[0,1]$
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 14(ii), p.44

import Mathlib
import Definitions.Def_StableVotingDistortion_IsScoreFunction
import Definitions.Def_StableVotingDistortion_scorePrimitives
import Definitions.Def_StableVotingDistortion_VerifierHypotheses

set_option autoImplicit false

namespace StableVotingDistortion

/-- **Lemma 14(ii) (large masses).** Let `ϕ` satisfy (26) with `ϕ(r) + r` nonincreasing on `[λ, 1]`, and let
`λ < p₁ < 1`. Suppose `ϕ(r) = λ − r` on `[r₋, z₊]` with `r₋ < λ` and `λ + (1 − p₁) ≤ z₊`, that `ϕ` is concave on
`[λ, 1]`, and that (46) holds for constants `0 < m₀ < 1 ≤ M`. If (25) and (47) hold for every `p ∈ [p₁, 1)`, then
(37) and (38) hold for every `p ∈ [p₁, 1)` with `β(p) = p / J(p)` and
`c(p, x) = (λ − x − β(p)(1 − p) ϕ(x))₊`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), Lemma 14(ii), p.44: "(ii) Suppose that ϕ(r) = λ − r on an interval [r_−, z_+] with r_− < λ and
λ + (1 − p_1) ≤ z_+, that ϕ is concave on [λ, 1], and that for constants 0 < m_0 < 1 ≤ M, ϕ(r) − ϕ(s) ≤ m_0(s − r)
for 0 ≤ r < s ≤ r_−, ϕ(r) − ϕ(s) ≤ M(s − r) for p_1 ≤ r < s ≤ 1. (46) If, for every p ∈ [p_1, 1), Equation (25)
holds and m_0 p(1 − p) ≤ J(p) ≤ p(1 − p), p (1 − (M + 1)(1 − p)) ≥ (M − 1)J(p), (47) then Equations (37) and (38)
hold for every p ∈ [p_1, 1) with β(p) = p/J(p) and c(p, x) = (λ − x − β(p)(1 − p)ϕ(x))_+."

**Formalization Note.** `0 ≤ r₋` and `z₊ ≤ 1` say the interval lies in `ϕ`'s domain `[0, 1]`. `J(p) > 0` on
`[p₁, 1)` follows from (47), so `p / J(p)` is not a junk value there. `p₀` of the page's opening sentence
plays no part in (ii) and is not a binder. -/
theorem lemma_14_ii {lam : ℝ} {ϕ : ℝ → ℝ} (hϕ : IsScoreFunction lam ϕ)
    (hadd : AntitoneOn (fun r => ϕ r + r) (Set.Icc lam 1))
    {p1 : ℝ} (hp1lam : lam < p1) (hp1 : p1 < 1)
    {rm zp : ℝ} (hrm0 : 0 ≤ rm) (hzp1 : zp ≤ 1) (hrm : rm < lam) (hzp : lam + (1 - p1) ≤ zp)
    (hline : ∀ r ∈ Set.Icc rm zp, ϕ r = lam - r)
    (hconc : ConcaveOn ℝ (Set.Icc lam 1) ϕ)
    {m0 M : ℝ} (hm0 : 0 < m0) (hm01 : m0 < 1) (hM : 1 ≤ M)
    (h46a : ∀ r s, 0 ≤ r → r < s → s ≤ rm → ϕ r - ϕ s ≤ m0 * (s - r))
    (h46b : ∀ r s, p1 ≤ r → r < s → s ≤ 1 → ϕ r - ϕ s ≤ M * (s - r))
    (h25 : ∀ p ∈ Set.Ico p1 1, Eq25 lam ϕ p)
    (h47a : ∀ p ∈ Set.Ico p1 1, m0 * (p * (1 - p)) ≤ J ϕ p)
    (h47b : ∀ p ∈ Set.Ico p1 1, J ϕ p ≤ p * (1 - p))
    (h47c : ∀ p ∈ Set.Ico p1 1, (M - 1) * J ϕ p ≤ p * (1 - (M + 1) * (1 - p))) :
    ∀ p ∈ Set.Ico p1 1,
      Eq37 lam ϕ (fun p => p / J ϕ p)
          (fun p x => max (lam - x - p / J ϕ p * (1 - p) * ϕ x) 0) p ∧
        Eq38 lam ϕ (fun p => p / J ϕ p)
          (fun p x => max (lam - x - p / J ϕ p * (1 - p) * ϕ x) 0) p := by sorry

end StableVotingDistortion
