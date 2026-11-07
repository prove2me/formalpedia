-- Prove2me | Theorems.Thm_PFRelease_theorem_4_3
-- name    : PFRelease.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:08.035705+00:00
-- url     : https://prove2.me/theorems/d2b6dbfa-d1df-4f47-a75b-75a7ea0912ee
-- title:
--   Theorem 4.3 — the PFR theorem
-- statement:
--   Let $n\in\mathbb N$, $\varepsilon_1,\varepsilon_2\ge0$, $\delta_1,\delta_2,\delta_3\in[0,1]$, a friendliness predicate $F$, a filter $\mathcal F$ and a release mechanism $M$, and consider PFR $M\circ\mathcal F$ with respect to $F$. Suppose, on datasets of $n$ records:
--
--   1. $\mathcal F$ is $(\varepsilon_1,\delta_1)$-JDP;
--   2. $M$ is $(\varepsilon_2,\delta_2)$-friendly-DP with respect to $F$;
--   3. for every $s\in\mathcal X^n$ and slot $i$ with $s_i\ne\perp$, the probability that $\mathcal F(s)$ retains $s_i$ while $F(\mathcal F(s)^{i\to\perp},s_i)=0$ is at most $\delta_3$.
--
--   Then $M\circ\mathcal F$ is
--   $$
--   \big(\varepsilon_1+\varepsilon_2,\ \delta_1+\delta_2+e^{\varepsilon_1+\varepsilon_2}\delta_3\big)\text{-DP}
--   $$
--   on datasets of $n$ records.
--
--   The theorem reduces the privacy of PFR to three checkable properties of its two stages; Theorem 4.5 verifies them for element–block filtering.
--
--   **Formalization Note** The filter is arbitrary, given by the probability mass function of its nulled set; $M$ has probability laws.
--
--   Differences from the source:
--   - reading: PFR $M\circ\mathcal F$ with respect to $F$ (Definition 4.2: the filter retains a record, except with small probability, only if it is friendly with the remaining filtered data) → an arbitrary filter, with the informal requirement replaced by hypothesis 3 with parameter $\delta_3$; reason: the page states that the theorem quantifies the requirements of Definition 4.2, and hypothesis 3 is that quantification
--   - encoding: the filter's random output $\mathcal F(s)=s^{I\to\perp}$ → the probability mass function of the nulled index set $I$ on `Finset (Fin n)`, compared on datasets through `jdpLeft`/`jdpRight` and composed with $M$ as the finite mixture `compose`; reason: a filter is determined by the law of $I$; JDP is still compared on every set of datasets
--   - encoding: a randomized mechanism $M$ → the family of output laws $M(s)$, probability measures on a measurable space $Y$; reason: a randomized mechanism is its family of output laws; events are measurable sets
--   - encoding: datasets $s\in\mathcal X^n$ with null record $\perp$, slots $1,\dots,n$ → `Fin n → Option X` with `none` $=\perp$, slots $0,\dots,n-1$; reason: same objects
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem 4.3, p.12 (PDF p.14); restated as Theorem C.1, p.34

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_PFRelease_IsJDP
import Definitions.Def_PFRelease_IsFriendlyDP
import Definitions.Def_PFRelease_compose

open MeasureTheory

namespace PFRelease

/-- **Theorem 4.3 (PFR theorem)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem 4.3, p.12 = PDF p.14; restated as Theorem
C.1, p.34). Given `n ∈ ℕ`, `ε₁, ε₂ ≥ 0`, `δ₁, δ₂, δ₃ ∈ [0, 1]`, a friendliness predicate `F` and
PFR `M ∘ F` with respect to `F`: if the filter `F` is `(ε₁, δ₁)`-JDP and `M` is
`(ε₂, δ₂)`-friendly-DP with respect to `F`, both on datasets of `n` records, and for every
`s ∈ Xⁿ` and slot `i` with `sᵢ ≠ ⊥` the probability that `F(s)` retains `sᵢ` while
`F(F(s)^{i→⊥}, sᵢ) = 0` is at most `δ₃`, then `M ∘ F` is `(ε₁ + ε₂, δ₁ + δ₂ + e^{ε₁+ε₂}δ₃)`-DP on
datasets of `n` records.

**Formalization Note** The filter is arbitrary: `Fil s I` is the probability that it returns
`s^{I→⊥}` on input `s`, a probability mass function for every `s`. Definition 4.2's informal
requirement ("except with small probability") is exactly the quantitative `δ₃` hypothesis, so no
separate "is PFR" predicate is imposed. "`F(s)` retains `sᵢ`" is `i ∉ I`. `M s` is a probability
law for every `s`. -/
theorem theorem_4_3 {X Y : Type*} [MeasurableSpace Y] (n : ℕ) (ε₁ ε₂ δ₁ δ₂ δ₃ : ℝ)
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hδ₁0 : 0 ≤ δ₁) (hδ₁1 : δ₁ ≤ 1) (hδ₂0 : 0 ≤ δ₂) (hδ₂1 : δ₂ ≤ 1)
    (hδ₃0 : 0 ≤ δ₃) (hδ₃1 : δ₃ ≤ 1) (F : List (Option X) → Option X → Bool)
    (Fil : (Fin n → Option X) → Finset (Fin n) → ENNReal) (hFil : ∀ s, ∑ I, Fil s I = 1)
    (M : (Fin n → Option X) → Measure Y) (hM : ∀ s, IsProbabilityMeasure (M s))
    (hJDP : IsJDP Fil ε₁ δ₁) (hFDP : IsFriendlyDP M F ε₂ δ₂)
    (hδ₃ : ∀ (s : Fin n → Option X) (i : Fin n), s i ≠ none →
      ∑ I ∈ Finset.univ.filter
          (fun I => i ∉ I ∧ F (toList (nullOut (nullOut s I) {i})) (s i) = false), Fil s I
        ≤ ENNReal.ofReal δ₃) :
    IsDPOn (compose M Fil) (ε₁ + ε₂) (δ₁ + δ₂ + Real.exp (ε₁ + ε₂) * δ₃) := by sorry

end PFRelease
