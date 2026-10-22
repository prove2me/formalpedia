-- Prove2me | Theorems.Thm_PermPartialTranspose_CommonSolutions_appendix_b_high_dim
-- name    : PermPartialTranspose.CommonSolutions.appendix_b_high_dim
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:29.563155+00:00
-- url     : https://prove2.me/theorems/ea657a9b-c37b-4fca-aa6e-3b7d8ed089f6
-- title:
--   Appendix B (corrected): exclusion above dimension two
-- statement:
--   Let $d>2$, $a\ne0$, and $\check R(u)=a\mathbf1+uP+bP_*$. Then:
--
--   1. For every $u\ne0$, $\check R(u)$ fails the braid relation.
--   2. With $u$ as the spectral parameter, this family fails the multiplicative Yang–Baxter equation (14).
--   3. If $b\ne0$, it fails the additive Yang–Baxter equation (15).
--
--   These are the higher-dimensional exclusions needed for the corrected classification.
--
--   **Formalization Note** The paper's unqualified braid and additive claims have counterexamples at $u=0$ and $b=0$, respectively. The first is its own $\mathbf1+vP_*$ solution in §6.1; the second is the rational family $a\mathbf1+uP$ in §3.2. The corrected guards are explicit here.
-- source:
--   Zhang, Kauffman & Werner, Permutation and Its Partial Transpose, arXiv:quant-ph/0606005v1, p. 37, Appendix B (corrected)

import Mathlib
import Definitions.Def_PermPartialTranspose_CommonSolutions_Ops

namespace PermPartialTranspose.CommonSolutions

/-- The corrected higher-dimensional exclusions in Appendix B, p. 37. -/
theorem appendix_b_high_dim (d : ℕ) (hd : 3 ≤ d) (a b : ℂ) (ha : a ≠ 0) :
    (∀ u : ℂ, u ≠ 0 → ¬ BraidRel (Rcheck d a u b)) ∧
    ¬ MultiplicativeYBE d a b ∧
    (b ≠ 0 → ¬ AdditiveYBE d a b) := by sorry

end PermPartialTranspose.CommonSolutions
