-- Prove2me | Theorems.Thm_QuasiPolyTrace_corollary_17
-- name    : QuasiPolyTrace.corollary_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:56.989275+00:00
-- url     : https://prove2.me/theorems/069bc539-fde0-4e67-97ec-fb32dbb72877
-- title:
--   Corollary 17 — in the shift case a linear low-frequency statistic still separates
-- statement:
--   Assume all hypotheses of Lemma 16 (an integer $R\ge250$; $f,g\ge0$ supported on $\{-R,\dots,R\}$ with $\|f\|_1,\|g\|_1\le\tfrac12$; $p\in(0,\tfrac14]$; $\tau\in(0,\tfrac14]$; an integer $\ell\le pR+\sqrt{Rp\log(1/\tau)}$ with $|f_b(\ell)-g_b(\ell)|\ge\tau$; $\sqrt{\log(1/\tau)/(Rp)}\le\pi/8$; the tail bound with a constant $c\ge1$), and assume Conclusion 2 of Lemma 16: some $\alpha\in\mathbb R$ has $|F_b(\xi)-G_b(\xi)e^{i\xi\alpha}|\le\tau^2$ at every angle $\xi\in(-\pi,\pi]$ that is an integer multiple of $2\pi/R^2$. Then
--
--   $$
--   \Big|\sum_j\big(f_b(j)-g_b(j)\big)\,e^{ij\,2\pi/R^2}\Big|\ \ge\ \frac{\tau}{R^2}-\tau^2 .
--   $$
--
--   In the induction this gives a separating statistic with a linear, low-frequency weighting when Lemma 16 lands in its shift case.
--
--   Differences from the source:
--   - encoding: under the assumptions of Lemma 16, if Conclusion 2) applies → every hypothesis of Lemma 16 and its Conclusion 2) as explicit hypotheses; reason: the corollary refers to the lemma; its hypotheses are restated verbatim
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Corollary 17, p.19

import Mathlib
import Definitions.Def_QuasiPolyTrace_binConv
import Definitions.Def_QuasiPolyTrace_fourier

namespace QuasiPolyTrace

open scoped Real

/-- **Corollary 17 (in the shift case, a linear low-frequency statistic still separates).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…),
Corollary 17, p.19: "Under the assumptions of Lemma 16, if Conclusion 2) applies, then we can further
conclude that |∑_j (f_b(j) − g_b(j)) · e^{ij 2π/R²}| ≥ τ/R² − τ²."

The hypotheses are those of Lemma 16 (p.18), and Conclusion 2) of Lemma 16 is assumed: there is
`α ∈ ℝ` with `|F_b(ξ) − G_b(ξ)e^{iξα}| ≤ τ²` at every angle `ξ ∈ (−π, π]` that is an integer multiple
of `2π/R²`.

**Formalization Note.** As in Lemma 16: `f, g` are nonnegative and supported on `[−R, R]`, so all sums over
`ℤ` are finite; `f_b = f ∗ Bin(R, p)`; logarithms are natural. -/
theorem corollary_17 (c : ℝ) (hc : 1 ≤ c) (R : ℕ) (f g : ℤ → ℝ) (p τ : ℝ) (ℓ : ℤ)
    (hR : 250 ≤ R) (hf0 : ∀ j, 0 ≤ f j) (hg0 : ∀ j, 0 ≤ g j)
    (hfs : ∀ j, f j ≠ 0 → -(R : ℤ) ≤ j ∧ j ≤ R) (hgs : ∀ j, g j ≠ 0 → -(R : ℤ) ≤ j ∧ j ≤ R)
    (hf1 : ∑' j, f j ≤ 1 / 2) (hg1 : ∑' j, g j ≤ 1 / 2) (hp0 : 0 < p) (hp1 : p ≤ 1 / 4)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 4)
    (hℓ : (ℓ : ℝ) ≤ p * R + Real.sqrt (R * p * Real.log (1 / τ)))
    (hdisc : τ ≤ |binConv f R p ℓ - binConv g R p ℓ|)
    (hu : Real.sqrt (Real.log (1 / τ) / (R * p)) ≤ π / 8)
    (htail : ∑' j : ℤ, |f j - g j| * Real.exp (-2 * j * Real.sqrt (Real.log (1 / τ) / (R * p)))
      ≤ 1 / τ ^ c)
    (hshift : ∃ α : ℝ, ∀ ξ : ℝ, -π < ξ → ξ ≤ π → (∃ m : ℤ, ξ = m * (2 * π / (R : ℝ) ^ 2)) →
        ‖fourier (fun j => ((binConv f R p j : ℝ) : ℂ)) ξ
          - fourier (fun j => ((binConv g R p j : ℝ) : ℂ)) ξ * Complex.exp (Complex.I * (ξ : ℂ) * (α : ℂ))‖
          ≤ τ ^ 2) :
    τ / (R : ℝ) ^ 2 - τ ^ 2 ≤
      ‖∑' j : ℤ, (((binConv f R p j - binConv g R p j : ℝ) : ℂ)
        * Complex.exp (Complex.I * (j : ℂ) * ((2 * π / (R : ℝ) ^ 2 : ℝ) : ℂ)))‖ := by sorry

end QuasiPolyTrace
