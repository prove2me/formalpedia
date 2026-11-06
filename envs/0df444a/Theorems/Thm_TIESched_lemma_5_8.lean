-- Prove2me | Theorems.Thm_TIESched_lemma_5_8
-- name    : TIESched.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:00.155897+00:00
-- url     : https://prove2.me/theorems/3e68158c-38d4-417c-9213-6a8dbc14fb84
-- title:
--   Lemma 5.8 — vanishing via Laplace transform
-- statement:
--   Let $J$ be a finite job set with $|J|\ge m$, $D=m|J|$, and let $f_i:[0,\infty)^D\to\mathbb R$, $i\in[m]$, satisfy the hypotheses of Lemma 5.8: differentiability along own-coordinate lines with strictly positive other coordinates (with a right derivative at $0$), continuity on $(0,\infty)^D$, bounded own-coordinate derivatives, the zero boundary condition $p_{ij}=0\Rightarrow f_i(p)=0$, and the differential conservation law $\sum_{i=1}^m\partial f_i(p)/\partial p_{ij}=0$. Then
--   $$f_i(p)=0\qquad\text{for all }i\in[m]\text{ and all }p\in(0,\infty)^D.$$
--
--   This analytic step forces the (smoothed) utility interactions of order at least $m$ to vanish.
--
--   Differences from the source:
--   - encoding: f_i : [0,∞)^D → ℝ → total functions on report matrices Fin m → J → ℝ whose values on the closed orthant are constrained; reason: values outside the orthant never enter
--   - encoding: ∂f_i/∂p_ij and the right derivative at 0 → deriv of the line function at p_ij, and DifferentiableWithinAt on [0, ∞) at each t ≥ 0; reason: the same derivatives; at t > 0 the set [0, ∞) is a neighbourhood of t
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma 5.8, p.26

import Mathlib
import Definitions.Def_TIESched_SatisfiesVanishingHyps

set_option autoImplicit false

namespace TIESched

/-- **Lemma 5.8 (Vanishing via Laplace transform)** (Wang, Xu, Zhang, arXiv:2611.05142, Lemma 5.8,
p.26). Let `J` be a finite job set with `|J| ≥ m`, `D = m|J|`, and let `f_i : [0, ∞)^D → ℝ`,
`i ∈ [m]`, be differentiable along each own-coordinate line whose other coordinates are strictly
positive, with a right derivative at the zero endpoint, and satisfy (1) continuity on `(0, ∞)^D`,
(2) bounded own-coordinate derivatives, (3) the zero boundary condition and (4) the differential
conservation law (3) (`SatisfiesVanishingHyps`). Then `f_i(p) = 0` for all `i ∈ [m]` and all
`p ∈ (0, ∞)^D`.

**Formalization Note.** The `f_i` are arbitrary real functions on report matrices; only their
values on the closed orthant enter the hypotheses. -/
theorem lemma_5_8 (m : ℕ) (hm : 2 ≤ m) (J : Finset ℕ) (hJ : m ≤ J.card)
    (f : Fin m → (Fin m → J → ℝ) → ℝ) (hf : SatisfiesVanishingHyps J f) :
    ∀ (i : Fin m) (p : Fin m → J → ℝ), (∀ i' j', 0 < p i' j') → f i p = 0 := by sorry

end TIESched
