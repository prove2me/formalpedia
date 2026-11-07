-- Prove2me | Theorems.Thm_PFRelease_fact_A_3
-- name    : PFRelease.fact_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:00.255468+00:00
-- url     : https://prove2.me/theorems/a67c4252-a661-4a6a-a6bb-c9207cf6d517
-- title:
--   Fact A.3 — Laplace mechanism and exact Laplace tails
-- statement:
--   Let $\sigma>0$ and let $\mathrm{Lap}(\sigma)$ be the centred Laplace distribution with density $(2\sigma)^{-1}e^{-|z|/\sigma}$.
--
--   1. For $\mu,\mu'\in\mathbb R$ with $|\mu-\mu'|\le1$, $\ \mu+\mathrm{Lap}(\sigma)\approx_{1/\sigma,0}\mu'+\mathrm{Lap}(\sigma)$.
--   2. If a real-valued function $q$ on datasets has sensitivity at most $1$ (that is, $|q(s)-q(s^{i\to\perp})|\le1$ for all zero-out neighbours), then the mechanism $s\mapsto q(s)+\mathrm{Lap}(\sigma)$ is $(1/\sigma,0)$-DP.
--   3. For every $a\ge0$,
--   $$
--   \Pr[\mathrm{Lap}(\sigma)>a]=\Pr[\mathrm{Lap}(\sigma)<-a]=\tfrac12e^{-a/\sigma},\qquad \Pr[|\mathrm{Lap}(\sigma)|>a]=e^{-a/\sigma}.
--   $$
--
--   The Laplace mechanism prices each test of the filter and of sparse vector, and the one-sided tails bound the overflow of the noisy cap and of the test noise of the changed slot.
--
--   **Formalization Note** $\mu+\mathrm{Lap}(\sigma)$ is the image of the published Laplace law under $z\mapsto\mu+z$.
--
--   Differences from the source:
--   - encoding: the random variable $\mu+\mathrm{Lap}(\sigma)$ → the image of $\mathrm{Lap}(\sigma)$ under $z\mapsto\mu+z$; reason: same law
--   - encoding: a real-valued function $q$ on datasets of all sizes → a function on the datasets of $n$ slots, for every $n$; reason: neighbours have the same number of slots, so sensitivity and DP are statements about each $n$ separately
--   - encoding: datasets $s\in\mathcal X^n$ with null record $\perp$, slots $1,\dots,n$ → `Fin n → Option X` with `none` $=\perp$, slots $0,\dots,n-1$; reason: same objects
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Fact A.3, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_PFRelease_Indist

open MeasureTheory

namespace PFRelease

/-- **Fact A.3 (Laplace mechanism)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Fact A.3, p.27 = PDF p.29).
Given `σ > 0` and `µ, µ′ ∈ ℝ` with `|µ − µ′| ≤ 1`, `µ + Lap(σ) ≈_{1/σ,0} µ′ + Lap(σ)`. In particular,
if the sensitivity of a real-valued function `q` on datasets is at most 1, then `q(·) + Lap(σ)` is
`(1/σ, 0)`-DP. Moreover, for every `a ≥ 0`, `Pr[Lap(σ) > a] = Pr[Lap(σ) < −a] = e^{−a/σ}/2` and
`Pr[|Lap(σ)| > a] = e^{−a/σ}`.

**Formalization Note** `µ + Lap(σ)` is the image of `Lap(σ)` (the published
`PrivLearn.Generic.laplace`) under `z ↦ µ + z`. The sensitivity of `q` is over zero-out
neighbours (§2, p.7): `|q(s) − q(s^{i→⊥})| ≤ 1` for every `s` and slot `i`. -/
theorem fact_A_3 {X : Type*} (σ : ℝ) (hσ : 0 < σ) :
    (∀ μ μ' : ℝ, |μ - μ'| ≤ 1 →
      Indist ((PrivLearn.Generic.laplace σ).map (fun z => μ + z))
        ((PrivLearn.Generic.laplace σ).map (fun z => μ' + z)) (1 / σ) 0) ∧
    (∀ (n : ℕ) (q : (Fin n → Option X) → ℝ),
      (∀ (s : Fin n → Option X) (i : Fin n), |q s - q (nullOut s {i})| ≤ 1) →
      IsDPOn (fun s => (PrivLearn.Generic.laplace σ).map (fun z => q s + z)) (1 / σ) 0) ∧
    (∀ a : ℝ, 0 ≤ a →
      PrivLearn.Generic.laplace σ (Set.Ioi a) = ENNReal.ofReal (Real.exp (-a / σ) / 2) ∧
      PrivLearn.Generic.laplace σ (Set.Iio (-a)) = ENNReal.ofReal (Real.exp (-a / σ) / 2) ∧
      PrivLearn.Generic.laplace σ {z | a < |z|} = ENNReal.ofReal (Real.exp (-a / σ))) := by sorry

end PFRelease
