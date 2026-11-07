-- Prove2me | Theorems.Thm_PFRelease_theorem_4_5_step_1
-- name    : PFRelease.theorem_4_5_step_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:56.403573+00:00
-- url     : https://prove2.me/theorems/dd6e020f-f98e-4095-bd25-3e7fbcb24c5c
-- title:
--   Proof of Theorem 4.5, Step 1 — the filter is $(\varepsilon/2,17\delta/32)$-JDP
-- statement:
--   Let $n,b\in\mathbb N$ with $n/b\in\mathbb N$, $\varepsilon\in(0,1]$, $\delta\in(0,1)$, and put
--   $$
--   L:=\ln(16/\delta),\qquad \sigma:=12/\varepsilon,\qquad \sigma':=108L/\varepsilon^{3/2},\qquad \kappa:=2\sigma L .
--   $$
--   For every acceptance threshold $t\ge0$ and every friendliness predicate $F$, the element–block filter $\mathcal F=\mathcal F_{b,t,\kappa,\sigma,\sigma'}(F;\cdot)$ (Algorithm 1) on datasets of $n$ records is $(\varepsilon/2,17\delta/32)$-JDP:
--   $$
--   \mathcal F(s)^{i\to\perp}\approx_{\varepsilon/2,\,17\delta/32}\mathcal F(s^{i\to\perp})\qquad\text{for every } s\in\mathcal X^n \text{ and slot } i .
--   $$
--
--   This is the first hypothesis of the PFR theorem (Theorem 4.3) for the parameters of Theorem 4.5, with $\varepsilon_1=\varepsilon/2$ and $\delta_1=17\delta/32$.
--
--   Differences from the source:
--   - generalization: the filter of Theorem 4.5, with $t=7n/(8b)$ and $F=F_{2\tau}(\varphi)$ → every threshold $t\ge0$ and every predicate $F$; reason: Step 1 uses neither the value of $t$ nor the form of $F$; the goal instantiates the statement at $t=7n/(8b)$, $F=F_{2\tau}(\varphi)$
--   - encoding: the filter's random output $\mathcal F(s)=s^{I\to\perp}$ → the probability mass function of the nulled index set $I$ on `Finset (Fin n)`, compared on datasets through `jdpLeft`/`jdpRight` and composed with $M$ as the finite mixture `compose`; reason: a filter is determined by the law of $I$; JDP is still compared on every set of datasets
--   - encoding: a uniformly random partition of $[n]$ into $m=n/b$ subsets of size $b$ → a uniform equipartition map $\pi:[n]\to[m]$ with fibres of size $b$; reason: each unordered partition has the same number $m!$ of labellings and no friend count depends on the labels, so the law of the run is the same
--   - encoding: $n,b\in\mathbb N$ with $n/b\in\mathbb N$; $\varepsilon^{3/2}$ → `0 < b`, `b ∣ n`; the real power `ε ^ (3/2 : ℝ)`; $t,\kappa$ real; reason: same instances (for $b=0$ the quotient $n/b$ is undefined)
--   - encoding: datasets $s\in\mathcal X^n$ with null record $\perp$, slots $1,\dots,n$ → `Fin n → Option X` with `none` $=\perp$, slots $0,\dots,n-1$; reason: same objects
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), proof of Theorem 4.5 (Theorem C.2), Step 1, pp.35–36 (PDF pp.37–38)

import Mathlib
import Definitions.Def_PFRelease_IsJDP
import Definitions.Def_PFRelease_filterLaw

open MeasureTheory

namespace PFRelease

/-- **Proof of Theorem 4.5, Step 1: joint differential privacy of the filter** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), proof of
Theorem 4.5 (Theorem C.2), Step 1, pp.35–36 = PDF pp.37–38). Given `n, b ∈ ℕ` with `n/b ∈ ℕ`,
`ε ∈ (0, 1]` and `δ ∈ (0, 1)`, with `L := ln(16/δ)`, `σ := 12/ε`, `σ′ := 108L/ε^{3/2}` and
`κ := 2σL`, the element–block filter `F_{b,t,κ,σ,σ′}(F; ·)` (Algorithm 1) on datasets of `n` records
is `(ε/2, 17δ/32)`-JDP: `F(s)^{i→⊥} ≈_{ε/2,17δ/32} F(s^{i→⊥})` for every `s` and `i`.

**Formalization Note** The page proves this for `t = 7n/(8b)` and `F = F_{2τ}(φ)`; the argument
uses neither, so the statement is for every acceptance threshold `t ≥ 0` and every predicate `F`
(a declared generalization that specializes to the page's claim). `b ∣ n` with `b > 0` encodes
`n/b ∈ ℕ`. `ε^{3/2}` is the real power. -/
theorem theorem_4_5_step_1 {X : Type*} (n b : ℕ) (hb : 0 < b) (hbn : b ∣ n) (ε δ t : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (ht : 0 ≤ t)
    (F : List (Option X) → Option X → Bool) :
    let L := Real.log (16 / δ)
    let σ := 12 / ε
    let σ' := 108 * L / ε ^ (3 / 2 : ℝ)
    let κ := 2 * σ * L
    IsJDP (filterLaw (n := n) b t κ σ σ' F) (ε / 2) (17 * δ / 32) := by sorry

end PFRelease
