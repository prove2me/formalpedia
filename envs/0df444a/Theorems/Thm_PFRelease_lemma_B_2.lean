-- Prove2me | Theorems.Thm_PFRelease_lemma_B_2
-- name    : PFRelease.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:45.681437+00:00
-- url     : https://prove2.me/theorems/36ec97c4-ccf2-41a3-b3fe-f95a602edbd1
-- title:
--   Lemma B.2 — target charging for adaptive Boolean interactions
-- statement:
--   Let $n,\kappa\in\mathbb N$, $\zeta>0$, $p\in(0,1]$, $a>0$ and $\delta_0\in(0,1)$. Consider an adaptive interaction of at most $n$ Boolean rounds with one of two neighbouring datasets that halts after its $\kappa$th answer equal to $1$. Suppose that after every preceding transcript the distributions of the next answer on the two datasets are
--   $$
--   \pi\,\mathbf 0+(1-\pi)\,\mathbf B^0\quad\text{and}\quad\pi\,\mathbf 0+(1-\pi)\,\mathbf B^1
--   $$
--   for a common weight $\pi\in[0,1]$, the constant-zero distribution $\mathbf 0$, and distributions $\mathbf B^0,\mathbf B^1$ on $\{0,1\}$ with $\mathbf B^0\approx_{\zeta,0}\mathbf B^1$ and $\min_z\Pr[\mathbf B^z=1]\ge p$. Then the transcripts on the two datasets are $(\varepsilon_{\rm tc},\delta_0+\delta^*(a))$-indistinguishable, where
--   $$
--   W(a):=\Big\lceil\frac{(1+a)\kappa}{p}\Big\rceil,\qquad \delta^*(a):=\exp\Big(-\frac{a^2\kappa}{2(1+a)}\Big),\qquad \varepsilon_{\rm tc}:=\frac{W(a)\zeta^2}{2}+\zeta\sqrt{2W(a)\ln(1/\delta_0)}.
--   $$
--
--   Its privacy cost depends on the number of answers equal to $1$, not on the number of rounds; with Lemma B.1 it gives the privacy of sparse vector.
--
--   **Formalization Note** The interaction is a halting rule on transcripts (common to both datasets) and next-answer laws `ans z u` on `Bool` for datasets $z\in\{0,1\}$; `interLaw` caps it at $n$ rounds. "Halts after its $\kappa$th answer equal to $1$" is that the rule halts at every transcript with $\kappa$ ones.
--
--   Differences from the source:
--   - encoding: an adaptive interaction of at most $n$ Boolean rounds with one of two neighbouring datasets → a halting rule on transcripts, common to both datasets, and next-answer laws `ans z u` on `Bool` for $z\in\{0,1\}$; the transcript law `interLaw` is capped at $n$ rounds; reason: this data determines the law of the transcript of every such interaction
--   - encoding: after every preceding transcript → after every transcript at which a round is asked (not halted, fewer than $n$ rounds), reachable or not; reason: the answer laws at other transcripts are never used, and an unreachable transcript can be declared halted without changing the law, so every instance of the source is covered
--   - encoding: $W(a)=\lceil(1+a)\kappa/p\rceil$ → the natural-number ceiling of the nonnegative real $(1+a)\kappa/p$; reason: equal to the integer ceiling on nonnegative reals
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Lemma B.2, pp.30–31 (PDF pp.32–33)

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_PFRelease_interLaw

open MeasureTheory

namespace PFRelease

/-- **Lemma B.2 (Target charging, following Theorem B.4 in [CL23])** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Lemma B.2,
pp.30–31 = PDF pp.32–33). Given `n, κ ∈ ℕ`, `ζ > 0`, `p ∈ (0, 1]`, `a > 0`, `δ₀ ∈ (0, 1)` and an
adaptive interaction of at most `n` Boolean rounds with one of two neighbouring datasets that halts
after its `κ`th answer equal to 1: if, after every preceding transcript, the distributions of the
next answer on the two datasets are `π·0 + (1 − π)B₀` and `π·0 + (1 − π)B₁` for a common weight
`π ∈ [0, 1]` and distributions `B₀ ≈_{ζ,0} B₁` on `{0, 1}` with `min_z Pr[B_z = 1] ≥ p`, then the
transcripts on the two datasets are `(ε_tc, δ₀ + δ*(a))`-indistinguishable, where
`W(a) := ⌈(1 + a)κ/p⌉`, `δ*(a) := exp(−a²κ/(2(1 + a)))`, `ε_tc := W(a)ζ²/2 + ζ√(2W(a) ln(1/δ₀))`.

**Formalization Note** The interaction is encoded by its halting rule `halt` (a function of the
transcript, common to both datasets) and by the law `ans z u` of the next answer on dataset
`z ∈ {0, 1}` (`Bool`) after the transcript `u`; `interLaw` caps it at `n` rounds. "Halts after
its `κ`th answer equal to 1" is `halt u = true` whenever `u` has `κ` ones. The decomposition is
required after every transcript at which a round is asked (not halted, fewer than `n` rounds).
`W(a)` is the natural-number ceiling of the nonnegative `(1 + a)κ/p`. -/
theorem lemma_B_2 (n κ : ℕ) (ζ p a δ₀ : ℝ) (hζ : 0 < ζ) (hp0 : 0 < p) (hp1 : p ≤ 1) (ha : 0 < a)
    (hδ₀0 : 0 < δ₀) (hδ₀1 : δ₀ < 1) (halt : List Bool → Bool)
    (hhalt : ∀ u : List Bool, u.count true = κ → halt u = true)
    (ans : Bool → List Bool → Measure Bool)
    (hdec : ∀ u : List Bool, halt u = false → u.length < n →
      ∃ π : ℝ, 0 ≤ π ∧ π ≤ 1 ∧ ∃ B : Bool → Measure Bool,
        (∀ z, IsProbabilityMeasure (B z)) ∧ Indist (B false) (B true) ζ 0 ∧
        (∀ z, ENNReal.ofReal p ≤ B z {true}) ∧
        ∀ z, ans z u = ENNReal.ofReal π • Measure.dirac false + ENNReal.ofReal (1 - π) • B z) :
    let W : ℝ := (⌈(1 + a) * κ / p⌉₊ : ℕ)
    Indist (interLaw n halt (ans false)) (interLaw n halt (ans true))
      (W * ζ ^ 2 / 2 + ζ * Real.sqrt (2 * W * Real.log (1 / δ₀)))
      (δ₀ + Real.exp (-(a ^ 2 * κ / (2 * (1 + a))))) := by sorry

end PFRelease
