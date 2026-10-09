-- Prove2me | Theorems.Thm_ProjReflGrad_Weak_lemma_2_1_ii
-- name    : ProjReflGrad.Weak.lemma_2_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:16:08.009045+00:00
-- url     : https://prove2.me/theorems/8cda1d4f-3876-4880-ba4d-7ba9b139de0e
-- title:
--   Lemma 2.1 (ii), p. 3 — $\|P_Mx-y\|^2\le\|x-y\|^2-\|x-P_Mx\|^2$ for $y\in M$
-- statement:
--   Let $H$ be a real Hilbert space, $M\subseteq H$ nonempty, closed and convex, $x\in H$, and let $P_M$ be the metric projection onto $M$. Then
--   $$\|P_Mx-y\|^2\le\|x-y\|^2-\|x-P_Mx\|^2\qquad\forall y\in M .$$
--
--   This strengthened nonexpansiveness of the projection is the basic estimate behind the energy inequality of Lemma 3.1.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 3, Lemma 2.1 (ii)

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

namespace ProjReflGrad.Weak

/-- Lemma 2.1 (ii) (Malitsky 2015, p. 3): for a nonempty closed convex `M` and `x ∈ H`,
`‖P_M x - y‖² ≤ ‖x - y‖² - ‖x - P_M x‖²` for every `y ∈ M`. -/
theorem lemma_2_1_ii {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : Set H) (hMne : M.Nonempty) (hMcl : IsClosed M) (hMcv : Convex ℝ M) (x : H) :
    ∀ y ∈ M, ‖proj M x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - ‖x - proj M x‖ ^ 2 := by sorry

end ProjReflGrad.Weak
