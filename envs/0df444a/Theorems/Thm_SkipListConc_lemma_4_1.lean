-- Prove2me | Theorems.Thm_SkipListConc_lemma_4_1
-- name    : SkipListConc.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:53:12.6976+00:00
-- url     : https://prove2.me/theorems/5a6288b3-67d7-457e-8965-050df61c8c2d
-- title:
--   Lemma 4.1 — horizontal steps of one search: $\mathrm{hor}(x)\le 1+N_R$ with $N_r\sim\mathrm{NB}(r,p)$
-- statement:
--   Fix $0<p<1$. Consider a fixed search for $x$ in a skip list over a finite key set $S\ni x$ in which the heights $H_y\ge1$ of all items are independent random variables, and the heights of the items other than $x$ satisfy
--   $$
--   \Pr[H_y\ge\ell+1\mid H_y\ge\ell]\ \ge\ p\qquad\text{for every item }y\ne x\text{ and level }\ell\ge1 .
--   $$
--   Then there are i.i.d. Bernoulli$(p)$ variables $\xi_1,\xi_2,\dots$ (on an extension of the probability space) with the following property. For $r\ge1$ let $N_r$ be the number of failures before the $r$-th success. Then, for every outcome,
--   $$
--   \mathrm{hor}(x)\ \le\ 1+N_R,\qquad R=H_{\max}-H_x+1,
--   $$
--   and the number of horizontal steps on level $H_x$ is at most $1+N_1$. For each fixed $r$, $N_r\sim\mathrm{NB}(r,p)$, i.e. $\Pr[N_r=k]=\binom{k+r-1}{k}p^r(1-p)^k$, and $N_r$ is nondecreasing in $r$.
--
--   Differences from the source:
--   - reading: "There are i.i.d. Bernoulli(p) variables ξ_1, ξ_2, …" with a bound "for every outcome" → ∃ a probability space Ω′, a measure-preserving π : Ω′ → Ω and i.i.d. Bernoulli(p) B_i on Ω′; the bounds hold for every ω′ with the heights evaluated at π ω′; reason: the proof draws randomness beyond the heights, so the variables live on an extension
--   - encoding: hazard Pr[H_y ≥ ℓ+1 | H_y ≥ ℓ] ≥ p → p · Pr[H_y ≥ ℓ] ≤ Pr[H_y ≥ ℓ+1] for ℓ ≥ 1; reason: equivalent where the conditional is defined, and trivially true where Pr[H_y ≥ ℓ] = 0
--   - encoding: heights of the items, integers ≥ 1 → measurable h y : Ω → ℕ with h y ≥ 1 on every outcome for y ∈ S; reason: the standing convention of §1.1 (heights H_x ≥ 1 are random variables)
--   - encoding: N_r → N_r valued in ℕ∞ (⊤ if fewer than r successes); trials indexed from 0; reason: defined on every outcome; the null event has probability 0
--   - reading: "In particular hor(x) − 1 is stochastically dominated by NB(R, p)" → not a separate clause; reason: R is random and not independent of the trials; the sentence glosses the pointwise bound hor(x) ≤ 1 + N_R
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.1, pp.20–21

import Mathlib
import Definitions.Def_SkipListConc_levelSteps
import Definitions.Def_SkipListConc_horSteps
import Definitions.Def_SkipListConc_failuresBefore

open MeasureTheory ProbabilityTheory

namespace SkipListConc

/-- Lemma 4.1 (horizontal steps of one search) (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip
Lists: Concentration Bounds*, STOC 2027 submission manuscript (sha256 f82c3d35…6dab6c), Lemma 4.1,
pp.20–21). Consider a fixed search for `x` in a skip list in which the heights of all items are
independent, and the heights of the items other than `x` satisfy
`Pr[H_y ≥ ℓ + 1 | H_y ≥ ℓ] ≥ p` for every item `y ≠ x` and level `ℓ`. There are i.i.d.
Bernoulli(`p`) variables `ξ_1, ξ_2, …` with the following property. For `r ≥ 1`, let `N_r` be the
number of failures before the `r`-th success. Then, for every outcome, `hor(x) ≤ 1 + N_R`
(`R = H_max − H_x + 1`), and the number of horizontal steps on level `H_x` is at most `1 + N_1`.
For each fixed `r`, `N_r ∼ NB(r, p)`, and `N_r` is nondecreasing in `r`.

**Formalization Note** Reading: the Bernoulli variables use randomness beyond the heights, so
they live on an extension `(Ω', P')` of the heights' space through a measure-preserving
`π : Ω' → Ω`, and "for every outcome" is every `ω' ∈ Ω'`. The hazard condition is in multiplied
form `p Pr[H_y ≥ ℓ] ≤ Pr[H_y ≥ ℓ + 1]` (equivalent where the conditional is defined). `N_r` is
`ℕ∞`-valued; `NB(r, p)` is `Pr[N_r = k] = C(k + r − 1, k) p^r (1 − p)^k`. Trials are indexed from
`0`. The final "in particular" sentence of the lemma is the paper's reading of the pointwise bound
and is not a separate clause. -/
theorem lemma_4_1 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) {α : Type} [LinearOrder α]
    (S : Finset α) (x : α) (hx : x ∈ S) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : α → Ω → ℕ) (hmeas : ∀ y, Measurable (h y))
    (hpos : ∀ y ∈ S, ∀ ω, 1 ≤ h y ω) (hind : iIndepFun (fun y : S => h y) P)
    (hhaz : ∀ y ∈ S, y ≠ x → ∀ ℓ : ℕ, 1 ≤ ℓ →
      ENNReal.ofReal p * P {ω | ℓ ≤ h y ω} ≤ P {ω | ℓ + 1 ≤ h y ω}) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
      (B : ℕ → Ω' → Bool),
      IsProbabilityMeasure P' ∧ MeasurePreserving π P' P ∧
      (∀ i, Measurable (B i)) ∧ iIndepFun B P' ∧
      (∀ i, P' {ω' | B i ω' = true} = ENNReal.ofReal p) ∧
      (∀ ω' : Ω', ((horSteps S (fun y => h y (π ω')) x : ℕ) : ℕ∞) ≤
        1 + failuresBefore B (S.sup (fun y => h y (π ω')) - h x (π ω') + 1) ω') ∧
      (∀ ω' : Ω', ((levelSteps S (fun y => h y (π ω')) x (h x (π ω')) : ℕ) : ℕ∞) ≤
        1 + failuresBefore B 1 ω') ∧
      (∀ r : ℕ, 1 ≤ r → ∀ k : ℕ,
        P' {ω' | failuresBefore B r ω' = k} =
          ENNReal.ofReal ((Nat.choose (k + r - 1) k : ℝ) * p ^ r * (1 - p) ^ k)) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ ω' : Ω', failuresBefore B r ω' ≤ failuresBefore B (r + 1) ω') := by sorry

end SkipListConc
