-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_conjugate_rectangle_construct
-- name    : QAlgorithms.Papers.Independent.Next46.P21.conjugate_rectangle_construct
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:36:38.876146+00:00
-- url     : https://prove2.me/theorems/d4ab1c21-3ee8-4bfc-8a02-a8aca378a798
-- title:
--   Effective covering of conjugate rectangles
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $x_0<x_1$ and $y_0<y_1$ be real endpoints, with $\delta=x_1-x_0$ and $\Delta=y_1-y_0$. If $\delta\Delta\ge(1+\sqrt2)^2$, the source's rescaling and floor construction returns integers $a,b$, with an exact arithmetic operation budget $N$, such that
--
--   $$
--   a+b\sqrt2\in[x_0,x_1],\qquad a-b\sqrt2\in[y_0,y_1],\qquad N\le C(1+|\log\delta|)^2.
--   $$
--
--   The construction repeatedly rescales by $\lambda=1+\sqrt2$ until $1<\delta\le\lambda$, applies the three floor-based candidates of Lemma 17(d), and reverses the scalings and coordinate exchanges. Arithmetic, comparisons and integer floors have unit cost; this is not a bit-runtime assertion for arbitrary real encodings. Fixed per-step budgets dominate the displayed primitive operations. The result provides both existence and an effective construction.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 6, Lemma 17: covering rectangles and effective construction

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Lemma 17, PDF pp.6-8: the concrete rescale/round construction terminates,
returns a feasible quadratic integer, and uses O((1+|log delta|)^2) exact arithmetic operations.
The absolute constant precedes every endpoint. -/
theorem conjugate_rectangle_construct :
    ∃ C : ℝ, 0 < C ∧ ∀ x0 x1 y0 y1 : ℝ,
      x0 < x1 → y0 < y1 →
      (1 + Real.sqrt 2) ^ 2 ≤ (x1 - x0) * (y1 - y0) →
      ∃ a : Zsqrtd 2, ∃ cost : ℕ,
        RectangleRun x0 x1 y0 y1 a cost ∧ a ∈ rectangleSolutions x0 x1 y0 y1 ∧
        (cost : ℝ) ≤ C * (1 + |Real.log (x1 - x0)|) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
