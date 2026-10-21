-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_conjugate_rectangle_both_parities
-- name    : QAlgorithms.Papers.Independent.Next46.P21.conjugate_rectangle_both_parities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:37:57.38399+00:00
-- url     : https://prove2.me/theorems/1c3526a5-298e-407c-9e5f-65019694c6bb
-- title:
--   Effective conjugate rectangles with either parity
-- statement:
--   There is an absolute constant $C>0$ such that, for every pair of real intervals with $x_0<x_1$, $y_0<y_1$ and
--
--   $$
--   (x_1-x_0)(y_1-y_0)\ge2(1+\sqrt2)^2,
--   $$
--
--   the source's two rescaled rectangle calls compute quadratic integers $\alpha_e=a_e+b_e\sqrt2$ and $\alpha_o=a_o+b_o\sqrt2$. Their constant coefficients $a_e$ and $a_o$ are respectively even and odd, and
--
--   $$
--   \alpha_e,\alpha_o\in[x_0,x_1],\qquad \alpha_e^\bullet,\alpha_o^\bullet\in[y_0,y_1].
--   $$
--
--   Their combined exact arithmetic budget $N$ satisfies $N\le C(1+|\log(x_1-x_0)|)^2$. The even output is obtained by multiplying a solution of the rescaled rectangle by $\sqrt2$, reversing the conjugate interval's sign; the odd output uses the same procedure on intervals translated by $-1$, then adds $1$. The computation uses the arithmetic and floor model of Lemma 17. This retains both parities and the effective conclusion.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 8, Corollary 19: prescribed parity in conjugate rectangles

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Corollary 19, PDF p.8: both prescribed parities, both conjugate intervals,
and the source's explicit two-call efficient construction. -/
theorem conjugate_rectangle_both_parities :
    ∃ C : ℝ, 0 < C ∧ ∀ x0 x1 y0 y1 : ℝ,
      x0 < x1 → y0 < y1 →
      2 * (1 + Real.sqrt 2) ^ 2 ≤ (x1 - x0) * (y1 - y0) →
      ∃ ae ao : Zsqrtd 2, ∃ cost : ℕ,
        ParityRun x0 x1 y0 y1 ae ao cost ∧
        ae ∈ rectangleSolutions x0 x1 y0 y1 ∧ Even ae.re ∧
        ao ∈ rectangleSolutions x0 x1 y0 y1 ∧ Odd ao.re ∧
        (cost : ℝ) ≤ C * (1 + |Real.log (x1 - x0)|) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
