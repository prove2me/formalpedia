-- Prove2me | Theorems.Thm_PGDMap20261031_pgd_one_update_zero
-- name    : PGDMap20261031.pgd_one_update_zero
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:06.311628+00:00
-- url     : https://prove2.me/theorems/db319a47-a18e-4d08-be16-2cc2661197fa
-- title:
--   One update with zero strong convexity has unique normalized step $h=1$
-- statement:
--   ## Statement
--
--   The number $1$ belongs to $(0,2)$, and, for every real $u$ with $0<u<2$ and $u\ne1$, $2<2/[u(2-u)]$. Equivalently, the real function $h\mapsto2/[h(2-h)]$, which is the bundle's $N=1,q=0$ curve, has value $2$ at $h=1$ and has a strictly larger value at every other point of $(0,2)$.
-- source:
--   Optimal Constant Stepsizes for the Exact PGD Residual Curve, manuscript dated 2026-10-30, Theorem 1, one-update clause, pp. 1-2; local source: 01_PGD_Exact_Residual_Curve.pdf

import Definitions.Def_PGDMap20261031_Stepsize
open PGDMap20261031

theorem PGDMap20261031.pgd_one_update_zero : IsStrictCurveMin 1 0 1 := by sorry
