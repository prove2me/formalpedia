-- Prove2me | Theorems.Thm_SoSLinAlg_WeakRank_upper_bound_sec_4_1
-- name    : SoSLinAlg.WeakRank.upper_bound_sec_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:30:48.235951+00:00
-- url     : https://prove2.me/theorems/a3aa7a07-37da-43dd-b22e-3191357e0b60
-- title:
--   §4.1 — degree-(2r+2) upper bound
-- statement:
--   Let $n>r\ge1$ be integers and let $A\in\mathbb R^{n\times n}$ satisfy $\operatorname{rank}A\ge r+1$. The system $\operatorname{WRank}_r^n(A)$ is $XY^\top=A$ in two independent $n\times r$ matrices of unrestricted real indeterminates. Write $\vdash_D S$ for a degree-at-most-$D$ sum-of-squares refutation of the polynomial system $S$, as in Definition 1.1.
--
--   Then
--   $$\vdash_{2r+2}\operatorname{WRank}_r^n(A).$$
--
--   This is the upper half of the exact-degree result. The statement retains the source's SoS conclusion; it does not additionally demand that the sum-of-squares term be zero.
--
--   Differences from the source:
--   - encoding: matrix entries indexed by [n] and [r] → entries indexed by Fin n and Fin r, and equations by pairs of indices; reason: zero-based finite indices enumerate precisely the same entries and equations
--   - encoding: the zero polynomial has degree minus infinity → totalDegree 0 = 0 at nonnegative upper bounds; reason: all bounds in this item are nonnegative, so the allowed polynomials are unchanged
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, §4.1 Upper Bound, PDF p.13 (printed p.11)

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_SoSRefutable
import Definitions.Def_SoSLinAlg_WeakRank_WRank

namespace SoSLinAlg.WeakRank

/-- §4.1, PDF p.13 (printed p.11): the SoS upper bound, with all source hypotheses. -/
theorem upper_bound_sec_4_1 {n r : ℕ} (hr : 0 < r) (hrn : r < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : r + 1 ≤ A.rank) :
    SoSRefutable (WRank r A) (2 * r + 2) := by sorry

end SoSLinAlg.WeakRank
