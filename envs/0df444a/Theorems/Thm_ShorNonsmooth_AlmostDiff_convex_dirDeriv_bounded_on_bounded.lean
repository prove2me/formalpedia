-- Prove2me | Theorems.Thm_ShorNonsmooth_AlmostDiff_convex_dirDeriv_bounded_on_bounded
-- name    : ShorNonsmooth.AlmostDiff.convex_dirDeriv_bounded_on_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T15:56:16.64616+00:00
-- url     : https://prove2.me/theorems/8d714c5a-ede6-4a25-a0b3-de13ede02c22
-- title:
--   Proof of Theorem 1.15 (p. 18) — directional derivatives of a convex function are uniformly bounded on bounded sets
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be convex and let $S \subset E_n$ be bounded. Then there is a constant $C$ such that for every $x \in S$ and every direction $v \in E_n$ the one-sided directional derivative
--
--   $$
--   f'_v(x) = \lim_{t \to 0+} \frac{f(x + t v) - f(x)}{t}
--   $$
--
--   exists (as a finite limit) and satisfies $|f'_v(x)| \le C\,\|v\|$.
--
--   In the proof of Theorem 1.15 this is the step from convexity to the Lipschitz condition (a) in the definition of almost differentiable functions.
--
--   **Formalization Note** "Uniformly bounded" is stated relative to the length of the direction: one constant $C$ works for all $x \in S$ and all $v$, with the bound $C\|v\|$ (equivalently, $|f'_v(x)| \le C$ for unit $v$).
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 18, proof of Theorem 1.15, second sentence

import Mathlib

namespace ShorNonsmooth.AlmostDiff

/-- Shor (1985), p. 18, proof of Theorem 1.15, second sentence: the directional derivatives of a
convex function `f` on `E_n` are uniformly bounded in any bounded set `S`. For every bounded `S`
there is a constant `C` such that at every `x ∈ S` and in every direction `v` the one-sided
directional derivative `f'_v(x) = lim_{t → 0+} (f(x + t v) - f(x)) / t` exists and satisfies
`|f'_v(x)| ≤ C ‖v‖`. -/
theorem convex_dirDeriv_bounded_on_bounded {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Bornology.IsBounded S) :
    ∃ C : ℝ, ∀ x ∈ S, ∀ v : EuclideanSpace ℝ (Fin n), ∃ d : ℝ,
      Filter.Tendsto (fun t : ℝ => (f (x + t • v) - f x) / t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds d) ∧ |d| ≤ C * ‖v‖ := by sorry

end ShorNonsmooth.AlmostDiff
