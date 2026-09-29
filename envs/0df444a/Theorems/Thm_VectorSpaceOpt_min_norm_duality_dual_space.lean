-- Prove2me | Theorems.Thm_VectorSpaceOpt_min_norm_duality_dual_space
-- name    : VectorSpaceOpt.min_norm_duality_dual_space
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:53:06.101256+00:00
-- url     : https://prove2.me/theorems/a73ad53c-a189-4a6e-bef3-f8dbb7613987
-- title:
--   Minimum norm duality in the dual space
-- statement:
--   This is the companion of the subspace duality theorem, with the roles of the space and its dual exchanged.
--
--   Let $M$ be a subspace of a real normed space $X$ and let $x^* \in X^*$ be at distance $d$ from $M^\perp$. Then
--
--   $$d \;=\; \min_{m^* \in M^\perp} \|x^* - m^*\| \;=\; \sup_{\substack{x \in M \\ \|x\| \le 1}} \langle x, x^*\rangle,$$
--
--   where the minimum on the left **is achieved** by some $m_0^* \in M^\perp$. If the supremum on the right is achieved by some $x_0 \in M$, then $x^* - m_0^*$ is **aligned** with $x_0$.
--
--   Note which side is attained. The right-hand supremum is the norm of $x^*$ restricted to $M$, and it need not be attained; the left-hand minimum always is, because the minimizer is constructed rather than approximated — take the Hahn–Banach extension $y^*$ of $x^*|_M$ to the whole space, which has $\|y^*\| = \|x^*\|_M$, and set $m_0^* = x^* - y^*$. That difference vanishes on $M$, so lies in $M^\perp$, and $\|x^* - m_0^*\| = \|x^*\|_M$.
--
--   This is the precise sense of the chapter's methodological rule: Hahn–Banach establishes the existence of *functionals*, not of vectors, so a minimum norm problem posed in a dual space has a guaranteed solution while the same problem posed in the primal space may not.
--
--   **Formalization Note.** The dual-side supremum is a real supremum over the set $\{\langle x, x^*\rangle : x \in M,\ \|x\| \le 1\}$, which always contains $0$ and is bounded by $\|x^*\|$, so no junk value arises. Alignment is stated through the published `aligned` definition; the clause is conditional on some $x_0 \in M$ of norm at most one attaining the value.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.8, Theorem 2, p. 121

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned

namespace VectorSpaceOpt

theorem min_norm_duality_dual_space {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (f : X →L[ℝ] ℝ) :
    ∃ g₀ : X →L[ℝ] ℝ, (∀ m ∈ M, g₀ m = 0) ∧
      (∀ g : X →L[ℝ] ℝ, (∀ m ∈ M, g m = 0) → ‖f - g₀‖ ≤ ‖f - g‖) ∧
      ‖f - g₀‖ = sSup {r : ℝ | ∃ x ∈ M, ‖x‖ ≤ 1 ∧ r = f x} ∧
      (∀ x₀ ∈ M, ‖x₀‖ ≤ 1 → f x₀ = ‖f - g₀‖ →
        VectorSpaceOpt_aligned x₀ (f - g₀)) := by sorry

end VectorSpaceOpt
