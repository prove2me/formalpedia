-- Prove2me | Theorems.Thm_SharpConsist_lemma_B_1_c
-- name    : SharpConsist.lemma_B_1_c
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:12:19.951686+00:00
-- url     : https://prove2.me/theorems/babac6f7-1b6a-4cf8-b014-fb109155e223
-- title:
--   Lemma B.1(c), Eq. (B.1) — ordering across branches
-- statement:
--   Fix $T\in[7/5,3/2]$ and an integer $m\ge32$, let $\delta=1/(64m)$ and $s=x+y$. Pointwise on $[0,1]\times[0,m]$,
--   $$K_\delta\ge F_\delta,\qquad \partial_iF_\delta-\partial_iK_\delta\ge16\,\delta e^{-s}\quad(i=x,y).$$
--   The first inequality makes the marginal of the final element $r$ nonnegative; the second makes it nonincreasing as old elements are added.
--
--   Differences from the source:
--   - encoding: partial derivatives ∂_x, ∂_y of the profiles → fderiv ℝ of the profile on ℝ × ℝ applied to (1, 0) or (0, 1); reason: the profiles are C¹ near the rectangle (Lemma B.1(b)), so these are the genuine partials
--   - encoding: v, w defined on [0, ∞) → v, w defined on ℝ by the quadratic/linear piece for t ≤ T; reason: every argument the statement evaluates is nonnegative (t = ω_m y ≥ 0, z between t and s ≥ 0)
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), Appendix B.2, Lemma B.1(c), Eq. (B.1), p.34

import Mathlib
import Definitions.Def_SharpConsist_Fdelta

namespace SharpConsist

/-- **Lemma B.1(c), Eq. (B.1) (across branches).** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), Appendix B.2, Lemma B.1(c), p.34.
Fix `T ∈ [7/5, 3/2]` and an integer `m ≥ 32`. Pointwise on `[0, 1] × [0, m]`, with `s = x + y` and
`δ = 1/(64m)`: `K_δ ≥ F_δ` and `∂_i F_δ − ∂_i K_δ ≥ 16δe^{−s}` for `i = x, y`.

**Formalization Note.** Partial derivatives are `fderiv ℝ` of the profile as a function on `ℝ × ℝ`
in the direction `(1, 0)` or `(0, 1)`; both profiles are `C¹` near the rectangle (Lemma B.1(b)). -/
theorem lemma_B_1_c (T : ℝ) (hT : T ∈ Set.Icc (7 / 5 : ℝ) (3 / 2)) (m : ℕ) (hm : 32 ≤ m) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) m,
      Fdelta T m p.1 p.2 ≤ Kdelta T m p.1 p.2 ∧
      ∀ e ∈ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)),
        16 * deltaM m * Real.exp (-(p.1 + p.2)) ≤
          fderiv ℝ (fun q : ℝ × ℝ => Fdelta T m q.1 q.2) p e -
            fderiv ℝ (fun q : ℝ × ℝ => Kdelta T m q.1 q.2) p e := by sorry

end SharpConsist
