-- Prove2me | Theorems.Thm_PFRelease_theorem_4_5
-- name    : PFRelease.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:34.572169+00:00
-- url     : https://prove2.me/theorems/12643c43-5cf4-4041-a508-19dee63d59e0
-- title:
--   Theorem 4.5 — PFR with element–block filtering is $(\varepsilon,\delta)$-DP once $n\ge400bL^2/\varepsilon^{3/2}$
-- statement:
--   Let $n,b\in\mathbb N$ with $n/b\in\mathbb N$, $\varepsilon\in(0,1]$, $\delta\in(0,1)$, a friendliness threshold $\tau>0$, a concave friendliness score $\varphi$, and a release mechanism $M$ that is $(\varepsilon/2,\delta/4)$-friendly-DP with respect to $F_\tau(\varphi)$ on datasets of $n$ records. Put
--   $$
--   L:=\ln(16/\delta),\quad t:=\frac{7n}{8b},\quad \sigma:=\frac{12}{\varepsilon},\quad \sigma':=\frac{108L}{\varepsilon^{3/2}},\quad \kappa:=2\sigma L .
--   $$
--   If
--   $$
--   n\ \ge\ \frac{400\,bL^2}{\varepsilon^{3/2}},
--   $$
--   then $\mathrm{PFR}_{b,t,\kappa,\sigma,\sigma'}(M,\varphi,\tau)=M\circ\mathcal F_{b,t,\kappa,\sigma,\sigma'}(F_{2\tau}(\varphi))$ is $(\varepsilon,\delta)$-DP on datasets of $n$ records.
--
--   This is the main result of the paper: a release mechanism that is private only on neighbouring pairs whose changed record is friendly with the rest of the data becomes differentially private on every input after element–block filtering, at a cost in the number of blocks that does not grow with $n$.
--
--   **Formalization Note** The PFR mechanism's law on input $s$ is the mixture of $M(s^{I\to\perp})$ over the law of the filter's nulled set $I$ (Algorithm 1 with a uniform random equipartition and independent Laplace noises).
--
--   Differences from the source:
--   - encoding: a randomized mechanism $M$ → the family of output laws $M(s)$, probability measures on a measurable space $Y$; reason: a randomized mechanism is its family of output laws; events are measurable sets
--   - encoding: the filter's random output $\mathcal F(s)=s^{I\to\perp}$ → the probability mass function of the nulled index set $I$ on `Finset (Fin n)`, compared on datasets through `jdpLeft`/`jdpRight` and composed with $M$ as the finite mixture `compose`; reason: a filter is determined by the law of $I$; JDP is still compared on every set of datasets
--   - encoding: a uniformly random partition of $[n]$ into $m=n/b$ subsets of size $b$ → a uniform equipartition map $\pi:[n]\to[m]$ with fibres of size $b$; reason: each unordered partition has the same number $m!$ of labellings and no friend count depends on the labels, so the law of the run is the same
--   - encoding: $n,b\in\mathbb N$ with $n/b\in\mathbb N$; $\varepsilon^{3/2}$ → `0 < b`, `b ∣ n`; the real power `ε ^ (3/2 : ℝ)`; $t,\kappa$ real; reason: same instances (for $b=0$ the quotient $n/b$ is undefined)
--   - encoding: datasets $s\in\mathcal X^n$ with null record $\perp$, slots $1,\dots,n$ → `Fin n → Option X` with `none` $=\perp$, slots $0,\dots,n-1$; reason: same objects
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem 4.5, p.13 (PDF p.15); restated with proof as Theorem C.2, pp.35–36

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_PFRelease_IsFriendlyDP
import Definitions.Def_PFRelease_compose
import Definitions.Def_PFRelease_IsScore
import Definitions.Def_PFRelease_IsConcave
import Definitions.Def_PFRelease_filterLaw

open MeasureTheory

namespace PFRelease

/-- **Theorem 4.5 (PFR with element–block filtering)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem 4.5, p.13 = PDF p.15;
restated as Theorem C.2, p.35). Given `n, b ∈ ℕ` with `n/b ∈ ℕ`, `ε ∈ (0, 1]`, `δ ∈ (0, 1)`, a
friendliness threshold `τ > 0`, a concave friendliness score `φ` and a release mechanism `M` that is
`(ε/2, δ/4)`-friendly-DP with respect to `F_τ(φ)` on datasets of `n` records, if
`n ≥ 400bL²/ε^{3/2}`, then `PFR_{b,t,κ,σ,σ′}(M, φ, τ) = M ∘ F_{b,t,κ,σ,σ′}(F_{2τ}(φ))` is `(ε, δ)`-DP on
datasets of `n` records, where `L := ln(16/δ)`, `t := 7n/(8b)`, `κ := 2σL`, `σ := 12/ε` and
`σ′ := 108L/ε^{3/2}`.

**Formalization Note** Datasets are `Fin n → Option X` (`none` = `⊥`); `M s` is the law of the
release on input `s`, a probability measure on a measurable space `Y`; the PFR mechanism's law is
the mixture `compose` of `M` over the filter's law `filterLaw` (Algorithm 1 with a uniform random
equipartition and independent Laplace noises). `b ∣ n` with `b > 0` encodes `n/b ∈ ℕ`. A concave
friendliness score is `IsScore φ ∧ IsConcave φ`. `ε^{3/2}` is the real power; `t`, `κ` are real. -/
theorem theorem_4_5 {X Y : Type*} [MeasurableSpace Y] (n b : ℕ) (hb : 0 < b) (hbn : b ∣ n)
    (ε δ τ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hτ : 0 < τ)
    (φ : List (Option X) → Option X → ENNReal) (hφ : IsScore φ) (hconc : IsConcave φ)
    (M : (Fin n → Option X) → Measure Y) (hM : ∀ s, IsProbabilityMeasure (M s))
    (hFDP : IsFriendlyDP M (predOf φ τ) (ε / 2) (δ / 4))
    (hn : 400 * (b : ℝ) * Real.log (16 / δ) ^ 2 / ε ^ (3 / 2 : ℝ) ≤ n) :
    let L := Real.log (16 / δ)
    let t := 7 * (n : ℝ) / (8 * (b : ℝ))
    let σ := 12 / ε
    let σ' := 108 * L / ε ^ (3 / 2 : ℝ)
    let κ := 2 * σ * L
    IsDPOn (compose M (filterLaw b t κ σ σ' (predOf φ (2 * τ)))) ε δ := by sorry

end PFRelease
