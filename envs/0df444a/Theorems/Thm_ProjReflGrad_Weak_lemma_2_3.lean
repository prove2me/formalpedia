-- Prove2me | Theorems.Thm_ProjReflGrad_Weak_lemma_2_3
-- name    : ProjReflGrad.Weak.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:58.133978+00:00
-- url     : https://prove2.me/theorems/62aa4c66-e423-452a-97f3-86c94c5749ed
-- title:
--   Lemma 2.3 (Opial), p. 3 — if $x_n\rightharpoonup x$ then $\liminf\|x_n-x\|<\liminf\|x_n-y\|$ for $y\ne x$
-- statement:
--   Let $H$ be a real Hilbert space and $(x_n)$ a sequence in $H$ with $x_n\rightharpoonup x$. Then for every $y\ne x$
--   $$\liminf_{n\to\infty}\|x_n-x\|<\liminf_{n\to\infty}\|x_n-y\| .$$
--
--   Opial's property of Hilbert spaces is what rules out two distinct weak cluster points in the proof of Theorem 3.2.
--
--   **Formalization Note.** Both liminfs are taken in $[0,\infty]$ (of $\|x_n-x\|$ and $\|x_n-y\|$ viewed as extended nonnegative reals), because a real-valued liminf in Lean returns a junk value for sequences that are not bounded. Weakly convergent sequences in a Hilbert space are bounded, so both liminfs are finite and this is the paper's inequality.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 3, Lemma 2.3 (Opial)

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

namespace ProjReflGrad.Weak

/-- Lemma 2.3 (Opial) (Malitsky 2015, p. 3): if `x_n ⇀ xs` then for every `y ≠ xs`,
`liminf ‖x_n - xs‖ < liminf ‖x_n - y‖` (liminfs taken in `[0, ∞]`). -/
theorem lemma_2_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (x : ℕ → H) (xs : H) (hx : IsWeakLimit x xs) :
    ∀ y : H, y ≠ xs →
      Filter.liminf (fun n => ENNReal.ofReal ‖x n - xs‖) Filter.atTop
        < Filter.liminf (fun n => ENNReal.ofReal ‖x n - y‖) Filter.atTop := by sorry

end ProjReflGrad.Weak
