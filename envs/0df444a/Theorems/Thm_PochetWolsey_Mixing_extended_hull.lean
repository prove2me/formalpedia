-- Prove2me | Theorems.Thm_PochetWolsey_Mixing_extended_hull
-- name    : PochetWolsey.Mixing.extended_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:59.272231+00:00
-- url     : https://prove2.me/theorems/41c93ace-cceb-4b30-b2cd-ee62a0f5b117
-- title:
--   Theorem 8.6 — extended formulation of the mixing hull
-- statement:
--   Let $K>0$ and $b\in\mathbb R^K$. Define $X^{MIX}_K(b)=\{(s,y)\in\mathbb R_+\times\mathbb Z^K:s+y_k\ge b_k\ \text{for all }k\}$, $f_0=0$, and $f_j=b_j-\lfloor b_j\rfloor$. Then $(s,y)\in\mathbb R\times\mathbb R^K$ belongs to $\operatorname{conv}(X^{MIX}_K(b))$ if and only if there are $\delta\in\mathbb R_+^{K+1}$ and $\mu\ge0$ such that
--   $$
--   s=\sum_{j=0}^Kf_j\delta_j+\mu,\qquad
--   y_k\ge\sum_{j=0}^K\lceil b_k-f_j\rceil\delta_j-\mu\quad(1\le k\le K),\qquad
--   \sum_{j=0}^K\delta_j=1.
--   $$
--   This is an exact projection equality for the entire unbounded convex hull.
--
--   **Formalization Note** The Lean statement expands both defining sets and the level function so that the standalone goal audit sees all constraints. They are definitionally the same as `mixingSet`, `level`, and `extendedProjection`. The distinguished index is `none`, and `some k` represents the book's index $k+1$. No restriction on the sign of $b$, no ordering or distinctness of its fractional parts, and no integrality restriction on projected $y$ is imposed.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 245–246 (PDF 259–260), Theorem 8.6

import Mathlib
import Definitions.Def_PochetWolsey_Mixing_Model
import Definitions.Def_PochetWolsey_Mixing_Extended

namespace PochetWolsey.Mixing

theorem extended_hull {K : ℕ} (hK : 0 < K) (b : Fin K → ℝ) :
    let f : Option (Fin K) → ℝ := fun j =>
      match j with
      | none => 0
      | some k => b k - (⌊b k⌋ : ℝ)
    convexHull ℝ
      {p : ℝ × (Fin K → ℝ) | 0 ≤ p.1 ∧
        (∀ k, ∃ z : ℤ, p.2 k = (z : ℝ)) ∧ ∀ k, b k ≤ p.1 + p.2 k} =
      {p : ℝ × (Fin K → ℝ) | ∃ δ : Option (Fin K) → ℝ, ∃ μ : ℝ,
        (∀ j, 0 ≤ δ j) ∧ 0 ≤ μ ∧ (∑ j, δ j) = 1 ∧
        p.1 = (∑ j, f j * δ j) + μ ∧
        ∀ k, (∑ j, (⌈b k - f j⌉ : ℝ) * δ j) - μ ≤ p.2 k} := by sorry

end PochetWolsey.Mixing
