-- Prove2me | Theorems.Thm_PrivOptTest_lemma_B_1
-- name    : PrivOptTest.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:04.476078+00:00
-- url     : https://prove2.me/theorems/7cc5fbce-b9ab-4fd6-8fac-2de815e43d8a
-- title:
--   Lemma B.1, p.40 — the vector Laplace mechanism (tail per coordinate)
-- statement:
--   Let $f:\mathcal X^n\to\mathbb R^d$ satisfy $\|f(X)-f(X')\|_1\le\Delta$ for all neighbouring $X,X'$, with $\Delta>0$, and let $\varepsilon>0$. Then $\tilde f(X)=f(X)+Z$ with $Z\sim\mathrm{Lap}(\Delta/\varepsilon)^{\otimes d}$, where $\mathrm{Lap}(s)$ has density $(2s)^{-1}e^{-|z|/s}$, is $\varepsilon$-differentially private, and for every $X$, every $\beta\in(0,1]$ and every coordinate $i$,
--   $$\Pr\Big[|\tilde f(X)_i-f(X)_i|\ge\frac{\Delta}{\varepsilon}\ln\frac1\beta\Big]\le\beta.$$
--
--   The mechanism is the privacy primitive of every release in Algorithms 1 and 2.
--
--   Differences from the source:
--   - reading: Pr[|f̃(X) − f(X)| ≥ (Δ/ε) log(1/β)] ≤ β for the vector deviation → the bound for each coordinate i; reason: the absolute value of a vector is undefined; in any joint norm the bound is false for d ≥ 2 (ℓ∞: probability 1 − (1 − β)^d > β), and the paper applies it coordinatewise with a union bound (proof of Theorem 3.11)
--   - reading: log → natural logarithm; reason: at ln the bound is exactly the Laplace tail
--   - encoding: sensitivity Δ, privacy ε → 0 < Δ and 0 < ε; reason: Lap(Δ/ε) has a density only for a positive scale
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma B.1, p.40

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory

namespace PrivOptTest

/-- **Lemma B.1** (Laplace mechanism, p.40). If `f : 𝒳ⁿ → ℝ^d` has `ℓ₁`-sensitivity at most `Δ`, then
`f̃(X) = f(X) + Z` with `Z ∼ Lap(Δ/ε)^{⊗d}` is ε-differentially private, and for every `X` and
`β ∈ (0, 1]`, `Pr[|f̃(X)_i − f(X)_i| ≥ (Δ/ε) ln(1/β)] ≤ β` for each coordinate `i`.
Source: Haghifam, Patel, Blum, Fanti, Ziani, *Should We Combine Our Data?*, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Lemma B.1, p.40.

**Formalization Note.** The tail bound is per coordinate: for `d ≥ 2` it is false for the joint
`ℓ_∞` deviation (probability `1 − (1 − β)^d`), and the paper applies it coordinatewise with a union bound
(proof of Theorem 3.11). `log` is the natural logarithm, at which the bound is an equality. `Δ > 0` and
`ε > 0` make `Lap(Δ/ε)` a distribution with a density. -/
theorem lemma_B_1 {D : Type} {n d : ℕ} (f : (Fin n → D) → Fin d → ℝ) (Δ ε : ℝ) (hΔ : 0 < Δ)
    (hε : 0 < ε)
    (hf : ∀ X X' : Fin n → D, PrivLearn.Generic.Neighbors X X' → ∑ i, |f X i - f X' i| ≤ Δ) :
    PrivLearn.Generic.IsDP (fun X => (Measure.pi fun _ : Fin d =>
        PrivLearn.Generic.laplace (Δ / ε)).map fun Z => f X + Z) ε ∧
      ∀ (X : Fin n → D) (β : ℝ), 0 < β → β ≤ 1 → ∀ i : Fin d,
        ((Measure.pi fun _ : Fin d => PrivLearn.Generic.laplace (Δ / ε)).map fun Z => f X + Z)
          {y | Δ / ε * Real.log (1 / β) ≤ |y i - f X i|} ≤ ENNReal.ofReal β := by sorry

end PrivOptTest
