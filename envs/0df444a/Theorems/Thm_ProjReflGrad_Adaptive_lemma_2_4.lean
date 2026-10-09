-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_lemma_2_4
-- name    : ProjReflGrad.Adaptive.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:21.099609+00:00
-- url     : https://prove2.me/theorems/61fd0c0a-e70a-49d6-a1e4-ab395caa33d9
-- title:
--   Lemma 2.4, p. 3 — projecting along the ray from P_M x through x returns P_M x
-- statement:
--   Let $H$ be a real Hilbert space, $M \subseteq H$ nonempty, closed and convex, $x \in H$ and $\bar x = P_M x$. Then for every $\lambda > 0$
--   $$P_M(\bar x + \lambda(x - \bar x)) = \bar x.$$
--
--   The lemma is used in case (d) of the proof of Lemma 4.3, to rewrite $x_n$ as the projection of a point on the segment $[x_n, x_{n-1} - \lambda_{n-1}F(y_{n-1})]$.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 3, Lemma 2.4

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Lemma 2.4 (Malitsky 2015, p. 3): for `M` nonempty, closed and convex, `x ∈ H` and
`x̄ = P_M x`, one has `P_M(x̄ + λ(x - x̄)) = x̄` for every `λ > 0`. -/
theorem lemma_2_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (M : Set H) (hne : M.Nonempty)
    (hcl : IsClosed M) (hcv : Convex ℝ M) (x : H) :
    ∀ l : ℝ, 0 < l → ProjReflGrad.Weak.proj M (ProjReflGrad.Weak.proj M x + l • (x - ProjReflGrad.Weak.proj M x)) = ProjReflGrad.Weak.proj M x := by sorry

end ProjReflGrad.Adaptive
