-- Prove2me | Theorems.Thm_QuasiPolyTrace_corollary_34
-- name    : QuasiPolyTrace.corollary_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:56.951022+00:00
-- url     : https://prove2.me/theorems/915e9974-6558-41ee-99e4-4ae5f5f6284d
-- title:
--   Corollary 34 — local deconvolution by $\mathrm{Bin}(R',P)$
-- statement:
--   Let $f:\mathbb Z\to\mathbb C$ be supported on an integer interval $[I_-,I_+]$ with $\sum_{j=I_-}^{I_+}|f(j)|\le1$, and let $\varepsilon,\delta>0$ be such that its Fourier transform $F$ satisfies $|F(\xi)|\le\delta$ for all $\xi\in[-\pi,\pi]$ with $|\xi|\ge\varepsilon$. Let $P\in(0,\tfrac14]$ and let $R'$ be a positive integer with
--
--   $$
--   e^{-0.16PR'+1}\le\delta\le e^{-4PR'\varepsilon^2}.
--   $$
--
--   Put $r=300\sqrt{R'P\lceil\log(1/\delta)\rceil}$. Then there is $g:\mathbb Z\to\mathbb C$ supported on $[I_--R'P-r,\ I_+-R'P+r]$ with $|g(j)|\le 11e^{R'P\varepsilon^2}$ for all $j$ and
--
--   $$
--   \big\|g*\mathrm{Bin}(R',P)-f\big\|_\infty\le 9\delta .
--   $$
--
--   A smooth weight sequence can be written, up to $9\delta$, as a binomial blur of a bounded, compactly supported sequence; this is how Proposition 37 moves from a window of size $R$ to one of size $R'\approx R^2$.
--
--   Differences from the source:
--   - encoding: e^{−0.16PR′+1} ≤ δ ≤ e^{−4PR′ε²} < 1 → e^{−0.16PR′+1} ≤ δ ≤ e^{−4PR′ε²}; reason: e^{−4PR′ε²} < 1 holds automatically for P, R′, ε > 0, so it excludes nothing
--   - encoding: support [I₋ − R′P − r, I₊ − R′P + r]; ⌈log(1/δ)⌉; ∥·∥_∞ → g j ≠ 0 → j in the real interval; natural-number ceiling; a bound at every integer j; reason: the endpoints are real numbers; log(1/δ) > 0 since δ < 1; the sup norm of a sequence on ℤ
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Corollary 34, pp.30–31

import Mathlib
import Definitions.Def_QuasiPolyTrace_binConv
import Definitions.Def_QuasiPolyTrace_fourier

namespace QuasiPolyTrace

open scoped Real

/-- **Corollary 34 (local deconvolution by a binomial).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Corollary 34, pp.30–31: "Let
f : Z → C supported on an interval [I₋, I₊] with ∑_{j=I₋}^{I₊} |f(j)| ≤ 1. Further, letting
F : [−π, π] → C be the Fourier transform of f, we assume that, for a given ε, δ > 0 we have that
|F(ξ)| ≤ δ when |ξ| ≥ ε. If for P ∈ (0, ¼] and positive integer R′ we have
e^{−0.16PR′+1} ≤ δ ≤ e^{−4PR′ε²} < 1 then there exists a g(x) that is 'an r-local deconvolution of f with
Bin(R′, P)' in the following sense: for r = 300√(R′P⌈log(1/δ)⌉) we have g is supported on
[I₋ − R′P − r, I₊ − R′P + r], with the pointwise bound |g(x)| ≤ 11 · e^{R′Pε²}, and,
∥g ∗ Bin(R′, P) − f∥_∞ ≤ 9δ."

**Formalization Note.**
* `g : ℤ → ℂ`; "supported on [a, b]" means `g j ≠ 0 → a ≤ j ≤ b` (the endpoints are real numbers).
* `F` is `fourier f` (Definition 4) at angles `ξ ∈ [−π, π]`; `f` is finitely supported, so its series is a
  finite sum.
* The clause `e^{−4PR′ε²} < 1` is not a separate hypothesis: it follows from `P, R′, ε > 0`.
* `⌈log(1/δ)⌉` is the natural-number ceiling (`log(1/δ) > 0` since `δ < 1`); logarithms are natural. -/
theorem corollary_34 (f : ℤ → ℂ) (Im Ip : ℤ) (hfs : ∀ j, f j ≠ 0 → Im ≤ j ∧ j ≤ Ip)
    (hf1 : ∑ j ∈ Finset.Icc Im Ip, ‖f j‖ ≤ 1) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hF : ∀ ξ : ℝ, -π ≤ ξ → ξ ≤ π → ε ≤ |ξ| → ‖fourier f ξ‖ ≤ δ)
    (P : ℝ) (hP0 : 0 < P) (hP1 : P ≤ 1 / 4) (R' : ℕ) (hR' : 0 < R')
    (hδlo : Real.exp (-0.16 * P * R' + 1) ≤ δ) (hδhi : δ ≤ Real.exp (-4 * P * R' * ε ^ 2)) :
    ∃ g : ℤ → ℂ,
      (∀ j, g j ≠ 0 →
        (Im : ℝ) - R' * P - 300 * Real.sqrt (R' * P * ⌈Real.log (1 / δ)⌉₊) ≤ j ∧
        (j : ℝ) ≤ Ip - R' * P + 300 * Real.sqrt (R' * P * ⌈Real.log (1 / δ)⌉₊)) ∧
      (∀ j, ‖g j‖ ≤ 11 * Real.exp (R' * P * ε ^ 2)) ∧
      ∀ j, ‖binConv g R' P j - f j‖ ≤ 9 * δ := by sorry

end QuasiPolyTrace
