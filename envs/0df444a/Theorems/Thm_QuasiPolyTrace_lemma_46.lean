-- Prove2me | Theorems.Thm_QuasiPolyTrace_lemma_46
-- name    : QuasiPolyTrace.lemma_46
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:00.607731+00:00
-- url     : https://prove2.me/theorems/40c26307-b86e-422d-885f-7568fdb194f3
-- title:
--   Lemma 46 — a compactly supported pmf with Fourier decay $8e^{-\varepsilon m/4}$
-- statement:
--   Let $m>0$ be an integer and $\varepsilon\in(0,1]$. There is $B:\mathbb Z\to\mathbb R_{\ge0}$ with $\sum_jB(j)=1$, supported on the open interval
--
--   $$
--   \Big(\frac m\varepsilon-\frac m2,\ \frac m\varepsilon+\frac m2\Big),
--   $$
--
--   whose Fourier transform satisfies $\big|\sum_jB(j)e^{ij\xi}\big|\le 8e^{-\varepsilon m/4}$ at every angle $\xi\in(-\pi,\pi]$ with $|\xi|\ge\varepsilon$.
--
--   This is the building block of the smooth weight function $w$ of Proposition 37 (through Lemma 47, which sums shifted copies of it).
--
--   Differences from the source:
--   - reading: B^{pdf} : Z → R≥⊬ → B : ℤ → ℝ with B ≥ 0; reason: the printed codomain is a typesetting glitch for R≥0; the proof constructs a probability mass function
--   - encoding: for any |ξ| ≥ ε → angles ξ ∈ (−π, π] with ε ≤ |ξ|; reason: the Fourier transform is a function of an angle (Definition 4); the proof uses |ξ| ≤ π
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 46, p.44

import Mathlib
import Definitions.Def_QuasiPolyTrace_fourier

namespace QuasiPolyTrace

open scoped Real

/-- **Lemma 46 (a compactly supported probability mass function with Fourier decay).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 46,
p.44: "Given integer m > 0 and real number ε ∈ (0, 1], there exists a function B^{pdf} : Z → R≥0 with sum 1
and supported on (m/ε − m/2, m/ε + m/2) such that for any |ξ| ≥ ε, the magnitude of the Fourier
transform of B^{pdf} is at most 8 · e^{−εm/4}."

**Formalization Note.**
* The PDF prints the codomain as `R≥⊬`, a typesetting glitch for `R≥0`; the proof makes `B^{pdf}` a
  probability mass function.
* The Fourier transform is that of Definition 4, at angles `ξ ∈ (−π, π]` (the proof uses `|ξ| ≤ π`).
* `B^{pdf}` is finitely supported, so its sum is a finite sum. -/
theorem lemma_46 (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ B : ℤ → ℝ, (∀ j, 0 ≤ B j) ∧ ∑' j, B j = 1 ∧
      (∀ j, B j ≠ 0 → (m : ℝ) / ε - m / 2 < j ∧ (j : ℝ) < m / ε + m / 2) ∧
      ∀ ξ : ℝ, -π < ξ → ξ ≤ π → ε ≤ |ξ| →
        ‖fourier (fun j => ((B j : ℝ) : ℂ)) ξ‖ ≤ 8 * Real.exp (-ε * m / 4) := by sorry

end QuasiPolyTrace
