-- Prove2me | Theorems.Thm_SoSLinAlg_WeakRank_theorem_2_1
-- name    : SoSLinAlg.WeakRank.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:31:06.210885+00:00
-- url     : https://prove2.me/theorems/0312e0da-fe30-43b5-ba04-5a543d2e2c37
-- title:
--   Theorem 2.1 — exact SoS degree of the Weak Rank Principle
-- statement:
--   Let $n>r\ge1$ be integers and let $A\in\mathbb R^{n\times n}$ satisfy $\operatorname{rank}A\ge r+1$. The system $\operatorname{WRank}_r^n(A)$ is $XY^\top=A$ in two independent $n\times r$ matrices of unrestricted real indeterminates. Write $\vdash_D S$ for a degree-at-most-$D$ sum-of-squares refutation of the polynomial system $S$, as in Definition 1.1.
--
--   Both conclusions hold:
--   $$\vdash_{2r+2}\operatorname{WRank}_r^n(A),\qquad
--   \forall D\in\mathbb N,\ D\le2r+1\Longrightarrow\neg\bigl(\vdash_D\operatorname{WRank}_r^n(A)\bigr).$$
--
--   Thus the least refutation degree is exactly $2r+2$. The conclusion concerns every real matrix of the specified rank, not only the identity or a fixed dimension. The refutations are polynomial identities using real sums of squares and arbitrary polynomial multipliers with the product-degree bounds of Definition 1.1.
--
--   Differences from the source:
--   - encoding: matrix entries indexed by [n] and [r] → entries indexed by Fin n and Fin r, and equations by pairs of indices; reason: zero-based finite indices enumerate precisely the same entries and equations
--   - encoding: the zero polynomial has degree minus infinity → totalDegree 0 = 0 at nonnegative upper bounds; reason: all bounds in this item are nonnegative, so the allowed polynomials are unchanged
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, Theorem 2.1, PDF p.7 (printed p.5); proof §4, PDF pp.13–19 (printed pp.11–17)

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
import Definitions.Def_SoSLinAlg_WeakRank_WRank

namespace SoSLinAlg.WeakRank

/-- Theorem 2.1, PDF p.7 (printed p.5). Both clauses, for every real A of rank ≥ r+1. -/
theorem theorem_2_1 {n r : ℕ} (hr : 0 < r) (hrn : r < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : r + 1 ≤ A.rank) :
    SoSRefutable (WRank r A) (2 * r + 2) ∧
      ∀ D : ℕ, D ≤ 2 * r + 1 → ¬ SoSRefutable (WRank r A) D := by sorry

end SoSLinAlg.WeakRank
