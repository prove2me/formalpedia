-- Prove2me | Theorems.Thm_PFRelease_theorem_4_5_step_2
-- name    : PFRelease.theorem_4_5_step_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:12.680274+00:00
-- url     : https://prove2.me/theorems/0e157236-e053-4e3d-937a-d0080ccd53c8
-- title:
--   Proof of Theorem 4.5, Step 2 — a retained record is $\tau$-friendly with the remaining data, except w.p. $\delta/32$
-- statement:
--   Assume the hypotheses of Theorem 4.5 on $n,b,\varepsilon,\delta,\tau$ and on the score: $n,b\in\mathbb N$ with $n/b\in\mathbb N$, $\varepsilon\in(0,1]$, $\delta\in(0,1)$, $\tau>0$, $\varphi$ a concave friendliness score, and
--   $$
--   n\ \ge\ \frac{400\,bL^2}{\varepsilon^{3/2}},\qquad L:=\ln(16/\delta).
--   $$
--   Let $\mathcal F$ be the filter $\mathcal F_{b,t,\kappa,\sigma,\sigma'}(F_{2\tau}(\varphi))$ with $t:=7n/(8b)$, $\sigma:=12/\varepsilon$, $\sigma':=108L/\varepsilon^{3/2}$ and $\kappa:=2\sigma L$. Then for every $s\in\mathcal X^n$ and every slot $i$ with $x:=s_i\ne\perp$,
--   $$
--   \Pr\big[\mathcal F(s)\text{ retains }x\ \text{ and }\ F_\tau(\varphi;\mathcal F(s)^{i\to\perp},x)=0\big]\ \le\ \frac{\delta}{32}.
--   $$
--
--   This is the last hypothesis of the PFR theorem (Theorem 4.3), with $\delta_3=\delta/32$; it controls only the noise of the changed slot and of the cap.
--
--   **Formalization Note** "Retains $x$" is $i\notin I$ for the nulled set $I$; $\mathcal F(s)^{i\to\perp}$ is the $n$-slot dataset $(s^{I\to\perp})^{i\to\perp}$.
--
--   Differences from the source:
--   - encoding: the filter's random output $\mathcal F(s)=s^{I\to\perp}$ → the probability mass function of the nulled index set $I$ on `Finset (Fin n)`, compared on datasets through `jdpLeft`/`jdpRight` and composed with $M$ as the finite mixture `compose`; reason: a filter is determined by the law of $I$; JDP is still compared on every set of datasets
--   - encoding: a uniformly random partition of $[n]$ into $m=n/b$ subsets of size $b$ → a uniform equipartition map $\pi:[n]\to[m]$ with fibres of size $b$; reason: each unordered partition has the same number $m!$ of labellings and no friend count depends on the labels, so the law of the run is the same
--   - encoding: $n,b\in\mathbb N$ with $n/b\in\mathbb N$; $\varepsilon^{3/2}$ → `0 < b`, `b ∣ n`; the real power `ε ^ (3/2 : ℝ)`; $t,\kappa$ real; reason: same instances (for $b=0$ the quotient $n/b$ is undefined)
--   - encoding: datasets $s\in\mathcal X^n$ with null record $\perp$, slots $1,\dots,n$ → `Fin n → Option X` with `none` $=\perp$, slots $0,\dots,n-1$; reason: same objects
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), proof of Theorem 4.5 (Theorem C.2), Step 2, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_PFRelease_Dataset
import Definitions.Def_PFRelease_IsScore
import Definitions.Def_PFRelease_IsConcave
import Definitions.Def_PFRelease_filterLaw

namespace PFRelease

/-- **Proof of Theorem 4.5, Step 2: a retained record is friendly with the remaining data**
(Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), proof of Theorem 4.5 (Theorem C.2), Step 2, p.36 = PDF p.38). Under the hypotheses of
Theorem 4.5 on `n, b, ε, δ, τ` and the concave score `φ`, with `L := ln(16/δ)`, `t := 7n/(8b)`,
`σ := 12/ε`, `σ′ := 108L/ε^{3/2}`, `κ := 2σL` and `n ≥ 400bL²/ε^{3/2}`: for every dataset `s` and slot
`i` with `x := sᵢ ≠ ⊥`, the probability that the filter `F = F_{b,t,κ,σ,σ′}(F_{2τ}(φ))` retains `x`
although `x` is not `τ`-friendly with `A := F(s)^{i→⊥}` is at most `δ/32`.

**Formalization Note** The filter's output `s^{I→⊥}` is represented by `I`; "retains `x`" is
`i ∉ I`, and "`x` is not `τ`-friendly with `A`" is `F_τ(φ; A, x) = 0`, with `A` the `n`-slot list
`(s^{I→⊥})^{i→⊥}`. -/
theorem theorem_4_5_step_2 {X : Type*} (n b : ℕ) (hb : 0 < b) (hbn : b ∣ n) (ε δ τ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hτ : 0 < τ)
    (φ : List (Option X) → Option X → ENNReal) (hφ : IsScore φ) (hconc : IsConcave φ)
    (hn : 400 * (b : ℝ) * Real.log (16 / δ) ^ 2 / ε ^ (3 / 2 : ℝ) ≤ n)
    (s : Fin n → Option X) (i : Fin n) (hi : s i ≠ none) :
    let L := Real.log (16 / δ)
    let t := 7 * (n : ℝ) / (8 * (b : ℝ))
    let σ := 12 / ε
    let σ' := 108 * L / ε ^ (3 / 2 : ℝ)
    let κ := 2 * σ * L
    ∑ I ∈ Finset.univ.filter
        (fun I => i ∉ I ∧ predOf φ τ (toList (nullOut (nullOut s I) {i})) (s i) = false),
      filterLaw b t κ σ σ' (predOf φ (2 * τ)) s I ≤ ENNReal.ofReal (δ / 32) := by sorry

end PFRelease
