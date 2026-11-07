-- Prove2me | Theorems.Thm_QuasiPolyTrace_lemma_10
-- name    : QuasiPolyTrace.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:09.421535+00:00
-- url     : https://prove2.me/theorems/3b210223-1d95-41d4-ae8f-640e50cd37c8
-- title:
--   Lemma 10 — 3-point linearity test on an integer interval
-- statement:
--   Let $\gamma>0$ be an integer and let $S\subseteq[-\gamma,\gamma]\cap\mathbb Z$ omit at most $\gamma/4-1$ integers of this interval. Let $\delta>0$ and let $H:S\to\mathbb R/2\pi\mathbb Z$ satisfy
--
--   $$
--   \big|H(x)+H(y)-H(x+y)\big|\le\delta\qquad\text{whenever }x,y,x+y\in S,
--   $$
--
--   where $|\cdot|$ is the distance to the nearest multiple of $2\pi$. Then there is $\alpha\in\mathbb R$ with
--
--   $$
--   \big|H(x)-\alpha x\big|\le 12\gamma\delta\qquad\text{for all }x\in S\text{ with }|x|\le\tfrac12\gamma .
--   $$
--
--   A robust version of BLR linearity testing on an integer interval; Lemma 13 applies it to the phase difference of two Fourier transforms.
--
--   Differences from the source:
--   - encoding: H : S → R mod 2π, |x − y| ≤ δ for values mod 2π → H : ℤ → AddCircle (2π), the norm of AddCircle (2π); reason: only the values of H on S enter the statement; the AddCircle norm is the distance mod 2π
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 10, p.13

import Mathlib

namespace QuasiPolyTrace

open scoped Real

/-- **Lemma 10 (3-point linearity test on an integer interval).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), Lemma 10, p.13: "For integer
γ > 0, let S ⊆ [−γ, γ] ∩ Z contain all but ≤ γ/4 − 1 integers from this interval. If for some δ > 0 a
function H : S → R mod 2π satisfies H(x) + H(y) ≈_δ H(x + y) whenever x, y, x + y ∈ S, then there is an
α ∈ R such that H(x) ≈_{12γδ} αx for all x ∈ S ∩ [−½γ, ½γ]." Here (p.13) "`x ≈_δ y` denote[s] that
`|x − y| ≤ δ`".

**Formalization Note.**
* "R mod 2π" is `AddCircle (2π)`, and `|x − y|` for such values is the norm of `x − y` there, the
  distance to the nearest multiple of `2π`.
* `H` is given on all of `ℤ`; only its values on `S` enter the statement.
* The count "all but ≤ γ/4 − 1 integers" is the real inequality
  `#([−γ, γ] ∩ ℤ \ S) ≤ γ/4 − 1`. -/
theorem lemma_10 (γ : ℕ) (hγ : 0 < γ) (S : Finset ℤ) (hS : S ⊆ Finset.Icc (-(γ : ℤ)) γ)
    (hcount : (((Finset.Icc (-(γ : ℤ)) γ) \ S).card : ℝ) ≤ (γ : ℝ) / 4 - 1)
    (δ : ℝ) (hδ : 0 < δ) (H : ℤ → AddCircle (2 * π))
    (hH : ∀ x y : ℤ, x ∈ S → y ∈ S → x + y ∈ S → ‖H x + H y - H (x + y)‖ ≤ δ) :
    ∃ α : ℝ, ∀ x ∈ S, |(x : ℝ)| ≤ (γ : ℝ) / 2 →
      ‖H x - ((α * x : ℝ) : AddCircle (2 * π))‖ ≤ 12 * γ * δ := by sorry

end QuasiPolyTrace
