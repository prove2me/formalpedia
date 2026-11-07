-- Prove2me | Theorems.Thm_QuasiPolyTrace_lemma_16
-- name    : QuasiPolyTrace.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:52.695902+00:00
-- url     : https://prove2.me/theorems/74e9d538-797a-4e5d-abf0-c7f375e47379
-- title:
--   Lemma 16 — a separating summed statistic of order $\le 3$, or an approximate shift
-- statement:
--   Let $c\ge1$. There is an exponent $K>0$, depending only on $c$, such that the following holds. Let $R\ge250$ be an integer, let $f,g:\mathbb Z\to\mathbb R_{\ge0}$ be supported on $\{-R,\dots,R\}$ with $\|f\|_1,\|g\|_1\le\tfrac12$, let $p\in(0,\tfrac14]$, and let $f_b=f*\mathrm{Bin}(R,p)$, $g_b=g*\mathrm{Bin}(R,p)$. Let $\tau\in(0,\tfrac14]$ and an integer $\ell\le pR+\sqrt{Rp\log(1/\tau)}$ satisfy $|f_b(\ell)-g_b(\ell)|\ge\tau$, assume $\sqrt{\log(1/\tau)/(Rp)}\le\pi/8$ and
--
--   $$
--   \sum_j|f(j)-g(j)|\,e^{-2j\sqrt{\log(1/\tau)/(Rp)}}\le\tau^{-c}.
--   $$
--
--   Then one of the following holds:
--
--   1. there are integers $\ell_1,\ell_2\ge0$ with $\big|\sum_j f_b(j)f_b(j+\ell_1)f_b(j+\ell_2)-g_b(j)g_b(j+\ell_1)g_b(j+\ell_2)\big|\ge(\tau/R)^K$, or an integer $\ell_1\ge0$ with $\big|\sum_j f_b(j)f_b(j+\ell_1)-g_b(j)g_b(j+\ell_1)\big|\ge(\tau/R)^K$;
--   2. there is $\alpha\in\mathbb R$ with $|F_b(\xi)-G_b(\xi)e^{i\xi\alpha}|\le\tau^2$ for every angle $\xi\in(-\pi,\pi]$ that is an integer multiple of $2\pi/R^2$, where $F_b,G_b$ are the Fourier transforms of $f_b,g_b$.
--
--   Differences from the source:
--   - reading: ≥ 1/poly_c(1/τ, R) → ≥ (τ/R)^K with K > 0 chosen after c and before R, f, g, p, τ, ℓ; reason: the subscript says the polynomial depends on c only; since R ≥ 250 and 1/τ ≥ 4, every inverse polynomial in 1/τ and R is at least such a power
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 16, p.18

import Mathlib
import Definitions.Def_QuasiPolyTrace_binConv
import Definitions.Def_QuasiPolyTrace_fourier

namespace QuasiPolyTrace

open scoped Real

/-- **Lemma 16 (an abrupt difference gives a summed statistic of order ≤ 3, or an approximate shift).**
Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 16, p.18: "Given an integer R ≥ 250 and sequences f, g : Z → R≥0 supported on
{−R, …, R} with ∥f∥₁, ∥g∥₁ ≤ ½, and a binomial distribution Bin(R, p) with p ∈ (0, ¼], then define the
binomially blurred versions of f, g by convolving with the binomial: let f_b := f ∗ Bin(R, p) and
g_b := g ∗ Bin(R, p). Then, if there exists a bound τ ∈ (0, ¼] and a location ℓ ≤ pR + √(Rp log(1/τ))
such that |f_b(ℓ) − g_b(ℓ)| ≥ τ, and if √(log(1/τ)/(Rp)) ≤ π/8 and the left tail of f − g is controlled
as ∑_j |f(j) − g(j)| · e^{−2j√((log 1/τ)/(Rp))} ≤ 1/τ^c for some constant c ≥ 1, then:
1) Either there exist offsets ℓ₀ = 0, ℓ₁ ≥ 0, ℓ₂ ≥ 0 such that
|∑_j f_b(j + ℓ₀)f_b(j + ℓ₁)f_b(j + ℓ₂) − g_b(j + ℓ₀)g_b(j + ℓ₁)g_b(j + ℓ₂)| ≥ 1/poly_c(1/τ, R), or the
analogous product of two terms ignoring ℓ₂;
2) Or there exists α ∈ R such that 'f_b is approximately a shifted version of g_b' in the sense that,
defining the Fourier transforms F_b(ξ) = ∑_j f_b(j) · e^{ijξ} and G_b defined correspondingly in terms of
g_b, then for all angles ξ ∈ (−π, π] that are integer multiples of 2π/R² we have
|F_b(ξ) − G_b(ξ) · e^{iξα}| ≤ τ²."

**Formalization Note.**
* "1/poly_c(1/τ, R)" is `(τ/R)^K` for an exponent `K > 0` chosen after `c` and before everything else
  (it may depend on `c` only). Since `R ≥ 250` and `1/τ ≥ 4`, every inverse polynomial in `1/τ` and
  `R` is at least such a power.
* All sequences are finitely supported (`f, g` on `[−R, R]`, `f_b, g_b` on `[−R, 2R]`), so every `tsum`
  over `ℤ` is a finite sum; `∥f∥₁ = ∑ f` since `f ≥ 0`.
* Offsets and locations are integers; logarithms are natural. -/
theorem lemma_16 (c : ℝ) (hc : 1 ≤ c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R : ℕ) (f g : ℤ → ℝ) (p τ : ℝ) (ℓ : ℤ),
      250 ≤ R → (∀ j, 0 ≤ f j) → (∀ j, 0 ≤ g j) →
      (∀ j, f j ≠ 0 → -(R : ℤ) ≤ j ∧ j ≤ R) → (∀ j, g j ≠ 0 → -(R : ℤ) ≤ j ∧ j ≤ R) →
      ∑' j, f j ≤ 1 / 2 → ∑' j, g j ≤ 1 / 2 → 0 < p → p ≤ 1 / 4 → 0 < τ → τ ≤ 1 / 4 →
      (ℓ : ℝ) ≤ p * R + Real.sqrt (R * p * Real.log (1 / τ)) →
      τ ≤ |binConv f R p ℓ - binConv g R p ℓ| →
      Real.sqrt (Real.log (1 / τ) / (R * p)) ≤ π / 8 →
      ∑' j : ℤ, |f j - g j| * Real.exp (-2 * j * Real.sqrt (Real.log (1 / τ) / (R * p))) ≤ 1 / τ ^ c →
      (∃ ℓ₁ ℓ₂ : ℤ, 0 ≤ ℓ₁ ∧ 0 ≤ ℓ₂ ∧ (τ / R) ^ K ≤
        |∑' j : ℤ, (binConv f R p j * binConv f R p (j + ℓ₁) * binConv f R p (j + ℓ₂)
          - binConv g R p j * binConv g R p (j + ℓ₁) * binConv g R p (j + ℓ₂))|) ∨
      (∃ ℓ₁ : ℤ, 0 ≤ ℓ₁ ∧ (τ / R) ^ K ≤
        |∑' j : ℤ, (binConv f R p j * binConv f R p (j + ℓ₁)
          - binConv g R p j * binConv g R p (j + ℓ₁))|) ∨
      (∃ α : ℝ, ∀ ξ : ℝ, -π < ξ → ξ ≤ π → (∃ m : ℤ, ξ = m * (2 * π / (R : ℝ) ^ 2)) →
        ‖fourier (fun j => ((binConv f R p j : ℝ) : ℂ)) ξ
          - fourier (fun j => ((binConv g R p j : ℝ) : ℂ)) ξ * Complex.exp (Complex.I * (ξ : ℂ) * (α : ℂ))‖
          ≤ τ ^ 2) := by sorry

end QuasiPolyTrace
