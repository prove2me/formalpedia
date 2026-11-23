-- Prove2me | Theorems.Thm_TIESharp_makespan_bounds_except_seven
-- name    : TIESharp.makespan_bounds_except_seven
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:52.610812+00:00
-- url     : https://prove2.me/theorems/0b560c67-abc4-446b-8ad6-7b7294bacfe5
-- title:
--   Load-estimate makespan bounds for at least eight machines and for four, five, and six
-- statement:
--   Let $y$ be any Bounded-Square slot-rounding law at a nonnegative profile $t$. The three load estimates give
--   $$\mathbb E[C_{\max}]\le 3\,\mathrm{OPT}(t),\qquad
--   \mathbb E[C_{\max}]\le\frac{105}{32}\,\mathrm{OPT}(t),\qquad
--   \mathbb E[C_{\max}]\le\frac{29}{8}\,\mathrm{OPT}(t)$$
--   for $n=4,5,6$, respectively, and
--   $$\mathbb E[C_{\max}]\le\frac{n+1}{2}\,\mathrm{OPT}(t)$$
--   for every $n\ge8$. Profiles with $\mathrm{OPT}(t)=0$ are included.
--
--   The seven-machine case is deliberately excluded here: it requires the separate refinement of Proposition 5.5 and Lemmas 5.6--5.8.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, Proposition 3.4 and equations (3.1)--(3.4), pp.11--12; explicit ratios and zero-OPT case, p.13; proof using Lemmas 5.2--5.4, p.25.

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw

set_option autoImplicit false

/-- The makespan bounds obtained by combining the three load estimates, apart from the
seven-machine refinement (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*,
arXiv:2611.05134, Proposition 3.4, pp.11–12, and the completion on p.13). -/
theorem TIESharp.makespan_bounds_except_seven (n m : ℕ) (hn : 2 ≤ n)
    (t : Fin n → Fin m → ℝ) (ht : TIESharp.Nonneg t)
    (y : (Fin m → Fin n) → ℝ) (hy : TIESharp.IsBSSlotLaw t y) :
    (8 ≤ n → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A
        ≤ ((n : ℝ) + 1) / 2 * TIESharp.opt t) ∧
    (n = 4 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A ≤ 3 * TIESharp.opt t) ∧
    (n = 5 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A
        ≤ 105 / 32 * TIESharp.opt t) ∧
    (n = 6 → ∑ A, y A * MatousekLP.Scheduling.makespan (Matrix.of t) A
        ≤ 29 / 8 * TIESharp.opt t) := by sorry
