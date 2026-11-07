-- Prove2me | Theorems.Thm_SmoothBerr_lemma_5_6
-- name    : SmoothBerr.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:01.130991+00:00
-- url     : https://prove2.me/theorems/0c2ce539-be52-46b0-9746-37dc4af9212d
-- title:
--   Imported Lemma 5.6 — Anderson's inequality: $\mathbb E f(\|T(z+m)\|_2^2)\le\mathbb E f(\|Tz\|_2^2)$
-- statement:
--   Let $z\sim\mathcal N(0,I_k)$ be a standard Gaussian vector, let $T\in\mathbb R^{d\times k}$ and $m\in\mathbb R^k$ be deterministic, and let $f:[0,\infty)\to[0,\infty]$ be nonincreasing and measurable. Then
--   $$
--   \mathbb E\big[f\big(\|T(z+m)\|_2^2\big)\big]\le\mathbb E\big[f\big(\|Tz\|_2^2\big)\big].
--   $$
--   Centering a Gaussian vector can only increase the expectation of a decreasing function of its (linearly transformed) squared norm. The paper imports this consequence of Anderson's inequality (T. W. Anderson, 1955; see also Lemma 28.9 of Lattimore–Szepesvári) and uses it in the proofs of Lemmas 5.7 and 5.8.
--
--   **Formalization Note** Expectations of $[0,\infty]$-valued functions are lower Lebesgue integrals, which are always defined.
--
--   Differences from the source:
--   - encoding: f : [0, ∞) → [0, ∞] nonincreasing and measurable → f : ℝ → [0, ∞] measurable and antitone on [0, ∞); reason: only the values on [0, ∞) enter; every such function on [0, ∞) extends measurably to ℝ (e.g. x ↦ f(|x|))
--   - encoding: E[·] of a [0, ∞]-valued function → lower Lebesgue integral ∫⁻ against stdGaussianVec k; reason: same value for nonnegative integrands
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Imported Lemma 5.6, Eq. (12), p.14

import Mathlib
import Definitions.Def_SmoothBerr_stdGaussianVec

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace SmoothBerr

/-- **Imported Lemma 5.6 (Anderson's inequality [3])** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Imported Lemma 5.6, Eq. (12), p.14).

Let `z` be a standard Gaussian vector in `ℝᵏ`, let `T ∈ ℝ^{d×k}` and `m ∈ ℝᵏ` be deterministic,
and let `f : [0, ∞) → [0, ∞]` be nonincreasing and measurable. Then
`E[f(‖T(z + m)‖₂²)] ≤ E[f(‖Tz‖₂²)]`.

**Formalization Note** `f` is a measurable function `ℝ → [0, ∞]` that is antitone on `[0, ∞)`;
only its values on `[0, ∞)` enter (a function on `[0, ∞)` extends to `ℝ`, e.g. by `f(|x|)`).
Expectations are lower Lebesgue integrals (`∫⁻`), so they are always defined and may be `∞`. The
squared norm `‖y‖₂²` is `y ⬝ᵥ y`. `T` may be rectangular of any shape. -/
theorem lemma_5_6 {k d : ℕ} (T : Matrix (Fin d) (Fin k) ℝ) (m : Fin k → ℝ) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hanti : AntitoneOn f (Set.Ici 0)) :
    ∫⁻ z, f ((T *ᵥ (z + m)) ⬝ᵥ (T *ᵥ (z + m))) ∂(stdGaussianVec k) ≤
      ∫⁻ z, f ((T *ᵥ z) ⬝ᵥ (T *ᵥ z)) ∂(stdGaussianVec k) := by sorry

end SmoothBerr
