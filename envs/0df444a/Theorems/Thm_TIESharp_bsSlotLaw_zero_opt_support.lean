-- Prove2me | Theorems.Thm_TIESharp_bsSlotLaw_zero_opt_support
-- name    : TIESharp.bsSlotLaw_zero_opt_support
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:22:41.509589+00:00
-- url     : https://prove2.me/theorems/0925e686-2c73-4c81-9b0a-930bd6bd8fd7
-- title:
--   Zero optimum forces zero makespan on the slot-law support
-- statement:
--   Suppose $\mathrm{OPT}(t)=0$ and $y$ is a Bounded-Square slot-rounding law. Every assignment $A$ with $y_A>0$ satisfies
--   $$C_{\max}(t,A)=0.$$
--   Indeed, every job has a zero-cost machine, and Bounded-Square assigns it only to such machines; slot rounding preserves this support condition.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134, final paragraph of the general-ratio argument, p.13; see also Proposition 5.5 proof, p.27.

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_IsBSSlotLaw

set_option autoImplicit false

/-- If the optimum is zero, every assignment supported by a Bounded-Square slot-rounding law
has zero makespan (Li, *Sharp Bounds for Truthful-in-Expectation Scheduling*,
arXiv:2611.05134, p.13). -/
theorem TIESharp.bsSlotLaw_zero_opt_support (n m : ℕ) (hn : 2 ≤ n)
    (t : Fin n → Fin m → ℝ) (ht : TIESharp.Nonneg t)
    (y : (Fin m → Fin n) → ℝ) (hy : TIESharp.IsBSSlotLaw t y)
    (hopt : TIESharp.opt t = 0) (A : Fin m → Fin n) (hA : 0 < y A) :
    MatousekLP.Scheduling.makespan (Matrix.of t) A = 0 := by sorry
