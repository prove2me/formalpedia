-- Prove2me | Theorems.Thm_VectorSpaceOpt_min_norm_duality_subspace
-- name    : VectorSpaceOpt.min_norm_duality_subspace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:52:06.727624+00:00
-- url     : https://prove2.me/theorems/35a6ed0b-9c62-47b5-b273-b3dfb25e552c
-- title:
--   Minimum norm duality for subspaces
-- statement:
--   Let $x$ be an element of a real normed linear space $X$ and let $d$ be its distance from a subspace $M$. Then
--
--   $$d \;=\; \inf_{m \in M} \|x - m\| \;=\; \max_{\substack{\|x^*\| \le 1 \\ x^* \in M^\perp}} \langle x, x^*\rangle,$$
--
--   where the maximum on the right **is achieved** by some $x_0^* \in M^\perp$. Moreover, if the infimum on the left is achieved by some $m_0 \in M$, then $x_0^*$ is **aligned** with the error $x - m_0$.
--
--   This is the principal result of the chapter and the normed-space analogue of the projection theorem. Note the asymmetry that the notation hides: the left side is an infimum that may not be attained, while the right side is a maximum that always is. Existence has moved to the dual problem, which is exactly why the source insists that minimum norm problems be formulated in a dual space when one wants a solution to exist.
--
--   Two consequences make the equality useful rather than merely elegant. Because the two problems share a value, solving either bounds the other; and because alignment can be characterized explicitly in most concrete spaces — through the equality case of Hölder's inequality in $L_p$, for instance — a solution of one problem often yields a solution of the other directly. Infinite-dimensional problems with finitely many constraints become finite-dimensional this way.
--
--   **Formalization Note.** The maximizer is exhibited: a functional $f_0$ with $\|f_0\| \le 1$, vanishing on $M$, with $f_0(x)$ equal to the infimum, together with the bound $f(x) \le \inf$ for every competing $f$ in the unit ball of $M^\perp$, and the alignment clause for any minimizing $m_0$. Alignment is stated through the published `aligned` definition. When $d = 0$ the zero functional witnesses every clause.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.8, Theorem 1, pp. 119–120

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned

namespace VectorSpaceOpt

theorem min_norm_duality_subspace {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (x : X) :
    ∃ f₀ : X →L[ℝ] ℝ, ‖f₀‖ ≤ 1 ∧ (∀ m ∈ M, f₀ m = 0) ∧
      f₀ x = (⨅ m : M, ‖x - (m : X)‖) ∧
      (∀ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 → (∀ m ∈ M, f m = 0) →
        f x ≤ ⨅ m : M, ‖x - (m : X)‖) ∧
      (∀ m₀ ∈ M, ‖x - m₀‖ = (⨅ m : M, ‖x - (m : X)‖) →
        VectorSpaceOpt_aligned (x - m₀) f₀) := by sorry

end VectorSpaceOpt
