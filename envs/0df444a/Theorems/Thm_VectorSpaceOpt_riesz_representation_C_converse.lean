-- Prove2me | Theorems.Thm_VectorSpaceOpt_riesz_representation_C_converse
-- name    : VectorSpaceOpt.riesz_representation_C_converse
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:51:17.616492+00:00
-- url     : https://prove2.me/theorems/b6273ec8-fcd9-43c3-8d33-5d414d5ceb3b
-- title:
--   Functions of bounded variation define bounded functionals on $C[a,b]$
-- statement:
--   This is the converse half of the Riesz representation theorem for $C[a,b]$. Let $v$ be a function of bounded variation on $[a, b]$. Then
--
--   $$f(x) = \int_a^b x(t)\, dv(t)$$
--
--   defines a bounded linear functional on $C[a,b]$: the Riemann–Stieltjes integral exists for every continuous $x$, the resulting map is linear, and it is bounded because
--
--   $$\left| \int_a^b x(t)\,dv(t) \right| \le \|x\| \cdot \operatorname{T.V.}(v),$$
--
--   so that $\|f\| \le \operatorname{T.V.}(v)$.
--
--   Together with the forward direction, this establishes that integration against functions of bounded variation is exactly the dual of $C[a,b]$ — every bounded functional arises this way, and every function of bounded variation gives one.
--
--   **Formalization Note.** The bound is stated as $\|f\| \le \operatorname{T.V.}(v)$; equality holds for the normalized representative produced by the forward theorem but can fail for a general (non-normalized) $v$ representing the same functional, so only the inequality is claimed here.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.5, Theorem 1 (converse), p. 115

import Mathlib
import Definitions.Def_VectorSpaceOpt_bv_stieltjes

namespace VectorSpaceOpt

theorem riesz_representation_C_converse (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → ℝ) (hv : BoundedVariationOn v (Set.Icc a b)) :
    ∃ f : C(Set.Icc a b, ℝ) →L[ℝ] ℝ,
      (∀ x : C(Set.Icc a b, ℝ),
        VectorSpaceOpt_is_rs_integral (Set.IccExtend hab x) v a b (f x)) ∧
      ‖f‖ ≤ VectorSpaceOpt_total_variation v a b := by sorry

end VectorSpaceOpt
