-- Prove2me | Theorems.Thm_ProdMixedTomo_fact_2_3
-- name    : ProdMixedTomo.fact_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:14:46.129067+00:00
-- url     : https://prove2.me/theorems/483dbef2-bb63-4c9b-bcde-cf98b29d80ce
-- title:
--   Fact 2.3 — $\epsilon$-contamination is $(1+c)\epsilon$-corruption with probability $1-e^{-\Omega(c^2\epsilon N/(1+c))}$
-- statement:
--   There is a universal constant $\kappa>0$ such that the following holds. Let $p,q$ be probability distributions on a standard Borel space with $d_{\mathrm{tv}}(p,q)\le\epsilon$, let $c>0$ and $N\in\mathbb N$. Then there is a coupling of a clean sample $S_g\sim p^N$ and a contaminated sample $S\sim q^N$ under which
--   $$
--   \Pr\bigl[\#\{i:\ S_i\ne S_{g,i}\}>(1+c)\epsilon N\bigr]\ \le\ \exp\Bigl(-\kappa\,\frac{c^2\epsilon N}{1+c}\Bigr).
--   $$
--   Equivalently, an $\epsilon$-contaminated set of $N$ samples from $p$ is, except with that probability, a $(1+c)\epsilon$-corrupted set of samples from $p$; it transfers guarantees in the corruption model to contaminated data.
--
--   Differences from the source:
--   - reading: "with probability … S is a (1 + c)ϵ-corrupted set of samples from p" → a coupling γ of p^N and q^N with γ{#differing positions > (1 + c)ϵN} ≤ exp(−κc²ϵN/(1 + c)); reason: "S is corrupted" asserts a clean i.i.d. S_g it is obtained from, a statement about a joint law (reading R10)
--   - reading: distributions p, q → probability measures on a standard Borel space; reason: on a measurable space whose σ-algebra does not separate points the claim fails (X = {a, b, c} with σ-algebra {∅, {a}, {b, c}, X}, p = δ_b, q = δ_c: d_tv = 0 yet every coupling puts all mass on a measurable rectangle containing differing points); every space the paper uses ({0,1}ⁿ, ℝⁿ) is standard Borel
--   - encoding: Ω(·) → ∃ κ > 0 before X, p, q, ϵ, c, N; reason: meaning of a universal constant; the page's n is the sample size N
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Fact 2.3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_ProdMixedTomo_Corruption

open Classical

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Fact 2.3, p.14 (PDF p.16). Let `S` be an `ϵ`-contaminated set of `N` samples from `p` (i.i.d.
from some `q` with `d_tv(p, q) ≤ ϵ`). Then for any `c > 0`, with probability at least
`1 − exp(−Ω(c²ϵN/(1 + c)))`, `S` is a `(1 + c)ϵ`-corrupted set of samples from `p`.

**Formalization Note.** Reading (coupling form): there is a universal `κ > 0` such that `S ∼ q^N`
can be coupled with a clean `S_g ∼ p^N` so that the number of positions where they differ exceeds
`(1 + c)ϵN` with probability at most `exp(−κc²ϵN/(1 + c))`. Distributions live on a standard Borel
space (on a measurable space whose σ-algebra does not separate points the claim fails, since the
event "S_g ≠ S" is not seen by the σ-algebra). -/
theorem fact_2_3 :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ (X : Type) [MeasurableSpace X] [StandardBorelSpace X]
      (p q : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure p]
      [MeasureTheory.IsProbabilityMeasure q] (ϵ c : ℝ) (N : ℕ),
      tvMeasure p q ≤ ϵ → 0 < c →
      ∃ γ : MeasureTheory.Measure ((Fin N → X) × (Fin N → X)),
        MeasureTheory.IsProbabilityMeasure γ ∧
        γ.map Prod.fst = MeasureTheory.Measure.pi (fun _ : Fin N => p) ∧
        γ.map Prod.snd = MeasureTheory.Measure.pi (fun _ : Fin N => q) ∧
        γ {z | (1 + c) * ϵ * N < ((Finset.univ.filter fun i => z.1 i ≠ z.2 i).card : ℝ)} ≤
          ENNReal.ofReal (Real.exp (-(κ * c ^ 2 * ϵ * N / (1 + c)))) := by sorry

end ProdMixedTomo
