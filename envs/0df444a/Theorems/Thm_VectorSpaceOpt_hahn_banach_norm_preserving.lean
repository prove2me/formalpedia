-- Prove2me | Theorems.Thm_VectorSpaceOpt_hahn_banach_norm_preserving
-- name    : VectorSpaceOpt.hahn_banach_norm_preserving
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:49:20.603497+00:00
-- url     : https://prove2.me/theorems/7d133d5f-5fc3-44ee-b881-f7c4b1c5b76d
-- title:
--   Norm-preserving extension of a bounded functional
-- statement:
--   Let $f$ be a bounded linear functional defined on a subspace $M$ of a real normed vector space $X$. Then $f$ extends to a bounded linear functional $F$ on all of $X$ **without increasing its norm**:
--
--   $$F = f \ \text{ on } M, \qquad \|F\| = \|f\|_M = \sup_{m \in M,\, m \neq 0} \frac{|f(m)|}{\|m\|}.$$
--
--   This is the Hahn–Banach theorem applied with the sublinear functional $p(x) = \|f\|_M\,\|x\|$.
--
--   The result is best read as an existence theorem for a minimization problem. Extending $f$ to the whole space is easy; the difficulty is that an arbitrary extension will generally be unbounded, or bounded with a norm strictly larger than $\|f\|_M$. The theorem says the minimum-norm extension exists *and* tells us its norm exactly. That is the pattern the whole chapter follows: Hahn–Banach supplies existence for dual problems in situations where the primal problem may have no solution at all.
--
--   **Formalization Note.** The functional on the subspace is a continuous linear map on the subtype carrying the induced norm, so its operator norm *is* the restricted norm $\|f\|_M$ and no separate supremum needs to be written. The subspace carries no closedness hypothesis; the degenerate case $M = \{0\}$ is included, where both norms are $0$.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.4, Corollary 1, p. 112

import Mathlib

namespace VectorSpaceOpt

theorem hahn_banach_norm_preserving {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (f : M →L[ℝ] ℝ) :
    ∃ F : X →L[ℝ] ℝ, (∀ m : M, F m = f m) ∧ ‖F‖ = ‖f‖ := by sorry

end VectorSpaceOpt
