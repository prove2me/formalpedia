-- Prove2me | Theorems.Thm_PGDMap20261031_step_two_update_zero
-- name    : PGDMap20261031.step_two_update_zero
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:09.386742+00:00
-- url     : https://prove2.me/theorems/8b584a0d-4dfe-4082-b34a-76c265a8a384
-- title:
--   Two-update balance: $h=3/2$, exact value $8/15$
-- statement:
--   ## Statement
--
--   At the natural horizon $N=2$, real step $h=3/2$, and real parameter $q=0$, the first branch is $A_2(3/2,0)=2/[(3/2)(4-3/2)]=8/15$, the second branch is $B_2(3/2,0)=2(1-3/2)^2/[1-(1-3/2)^4]=8/15$, and the curve value, defined here as $\max\{A_2(3/2,0),B_2(3/2,0)\}$, is also $8/15$. This conjunction makes no comparison with values at other steps.
-- source:
--   Optimal Constant Stepsizes for the Exact PGD Residual Curve, manuscript dated 2026-10-30, Theorem 1, two-update formula, p. 1; local source: 02_PGD_Optimal_Constant_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Stepsize
open PGDMap20261031

theorem PGDMap20261031.step_two_update_zero : branchA 2 (3 / 2) 0 = 8 / 15 ∧ branchB 2 (3 / 2) 0 = 8 / 15 ∧ curve 2 (3 / 2) 0 = 8 / 15 := by sorry
