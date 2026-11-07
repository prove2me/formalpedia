-- Prove2me | Theorems.Thm_QuasiPolyTrace_lemma_14
-- name    : QuasiPolyTrace.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:56.472203+00:00
-- url     : https://prove2.me/theorems/0e64b5e0-b8ed-400d-be8e-f94806a4b941
-- title:
--   Lemma 14 — an abrupt start forces a mostly non-negligible Fourier transform
-- statement:
--   Let $c,c'>0$ and $c''\in(0,1)$. There is an exponent $K>0$, depending only on $c,c',c''$, such that the following holds. Let $f:\mathbb Z\to\mathbb R$ with $\sum_j|f(j)|\le1$, let $R\ge1$ be an integer, $p\in(0,\tfrac14]$, $\tau\in(0,\tfrac12]$, and put
--
--   $$
--   u=\sqrt{\frac{\log(1/\tau)}{Rp}},\qquad f_b=f*\mathrm{Bin}(R,p).
--   $$
--
--   Suppose some integer $\ell\le Rp+c\sqrt{Rp\log(1/\tau)}$ has $|f_b(\ell)|\ge\tau$, that $\sum_j|f(j)|e^{-2uj}\le\tau^{-c}$, and that $c'u\le\pi$. Then the set of angles $\theta\in[-c'u,c'u]$ with
--
--   $$
--   \Big|\sum_j f_b(j)e^{ij\theta}\Big|\ \ge\ \tau^{K}
--   $$
--
--   has Lebesgue measure at least $c''\cdot 2c'u$.
--
--   A sequence that starts abruptly cannot have a mostly negligible (blurred) Fourier transform near $0$; Lemma 16 combines this with Lemma 13.
--
--   Differences from the source:
--   - reading: |F_b(e^{iθ})| ≥ 1/poly_{c,c′,c′′}(1/τ) → |F_b(e^{iθ})| ≥ τ^K with K > 0 chosen after c, c′, c′′ and before f, R, p, τ; reason: the subscript says the polynomial depends on c, c′, c′′ only; an inverse polynomial in 1/τ ≤ 1 is bounded below by such a power
--   - encoding: F_b(z) = ∑_j f_b(j) z^j at z = e^{iθ}; a c′′ fraction of θ ∈ [−c′u, c′u] → fourier f_b θ; Lebesgue measure ≥ c′′ · 2c′u; reason: z^j = e^{ijθ} on the unit circle; a fraction of an interval is its relative length
--   - encoding: Bin(R, p) with u = √(log(1/τ)/(Rp)); the series ∑|f(j)| and ∑|f(j)|e^{−2uj} bounded → R a positive integer; both series assumed summable; reason: u is undefined at R = 0; the paper's bounds on the series presuppose that they converge
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 14, p.16

import Mathlib
import Definitions.Def_QuasiPolyTrace_binConv
import Definitions.Def_QuasiPolyTrace_fourier

namespace QuasiPolyTrace

open MeasureTheory
open scoped Real

/-- **Lemma 14 (an abrupt start forces a mostly non-negligible Fourier transform).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 14,
p.16: "Let c, c′ > 0 and c′′ ∈ (0, 1) be constants. Given a sequence f : Z → R with
∑_{j=−∞}^{∞} |f(j)| ≤ 1, and a binomial distribution Bin(R, p) with p ∈ (0, ¼], define the binomially
blurred version of f by convolving with the binomial: let f_b := f ∗ Bin(R, p). Suppose there exists a
bound τ ∈ (0, ½], where, defining u := √(log(1/τ)/(Rp)), there exists an integer location
ℓ ≤ Rp + c√(Rp log(1/τ)) such that |f_b(ℓ)| ≥ τ, and suppose ∑_{j=−∞}^{∞} |f(j)|e^{−2uj} ≤ 1/τ^c. Then,
defining the series F_b(z) := ∑_{j=−∞}^{∞} f_b(j)z^j for complex z, we have |F_b(e^{iθ})| is at least
1/poly_{c,c′,c′′}(1/τ) for at least a c′′ fraction of the frequencies θ in the range [−c′u, c′u], assuming
c′u ≤ π."

**Formalization Note.**
* "1/poly_{c,c′,c′′}(1/τ)" is `τ^K` for an exponent `K > 0` chosen after `c, c′, c′′` and before
  everything else (it may depend on the three constants only).
* `F_b(e^{iθ}) = ∑_j f_b(j) e^{ijθ}` is `fourier f_b θ`.
* "a c′′ fraction of θ ∈ [−c′u, c′u]" is Lebesgue measure at least `c′′ · 2c′u`.
* `R` is a positive integer (`u` is undefined at `R = 0`). The two series `∑|f(j)|` and
  `∑|f(j)|e^{−2uj}` are assumed summable; the paper's bounds on them presuppose that they converge.
* Logarithms are natural. -/
theorem lemma_14 (c c' c'' : ℝ) (hc : 0 < c) (hc' : 0 < c') (hc''₀ : 0 < c'') (hc''₁ : c'' < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℤ → ℝ) (R : ℕ) (p τ : ℝ) (ℓ : ℤ),
      Summable (fun j => |f j|) → ∑' j, |f j| ≤ 1 →
      0 < R → 0 < p → p ≤ 1 / 4 → 0 < τ → τ ≤ 1 / 2 →
      (ℓ : ℝ) ≤ R * p + c * Real.sqrt (R * p * Real.log (1 / τ)) →
      τ ≤ |binConv f R p ℓ| →
      Summable (fun j : ℤ => |f j| * Real.exp (-2 * Real.sqrt (Real.log (1 / τ) / (R * p)) * j)) →
      ∑' j : ℤ, |f j| * Real.exp (-2 * Real.sqrt (Real.log (1 / τ) / (R * p)) * j) ≤ 1 / τ ^ c →
      c' * Real.sqrt (Real.log (1 / τ) / (R * p)) ≤ π →
      ENNReal.ofReal (c'' * (2 * (c' * Real.sqrt (Real.log (1 / τ) / (R * p))))) ≤
        volume {θ ∈ Set.Icc (-(c' * Real.sqrt (Real.log (1 / τ) / (R * p))))
            (c' * Real.sqrt (Real.log (1 / τ) / (R * p))) |
          τ ^ K ≤ ‖fourier (fun j => ((binConv f R p j : ℝ) : ℂ)) θ‖} := by sorry

end QuasiPolyTrace
