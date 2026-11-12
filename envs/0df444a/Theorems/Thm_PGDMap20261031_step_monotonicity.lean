-- Prove2me | Theorems.Thm_PGDMap20261031_step_monotonicity
-- name    : PGDMap20261031.step_monotonicity
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:02.491414+00:00
-- url     : https://prove2.me/theorems/f980426f-91cb-4c7f-86ce-273d449cf9ed
-- title:
--   Monotonicity in strong convexity and horizon
-- statement:
--   ## Statement
--
--   For natural $N$ and real $q,h$, write $A_N(h,q)=2/[h(2N-h)]$ if $q=0$ and $A_N(h,q)=2q/[(1+hq)^{2N}-1-h^2q]$ otherwise, and $B_N(h,q)=2(1+q)(1-h)^{\,2N-2}/[(1+hq)^{2N}-(1-h)^{2N}]$, where the exponent $2N-2$ is truncated at $0$. Write $C_N(h,q)=2/[h(2-h+hq)]$ if $N=1$, and $\max\{A_N(h,q),B_N(h,q)\}$ otherwise, and define $H_N(q)=\inf\{h\in\mathbb R:1<h<2,\ A_N(h,q)=B_N(h,q)\}$ using the total real infimum operation (in particular, the infimum of the empty set is $0$); all real division, including division by zero, is total, with $a/0=0$. For every natural $N\ge2$ and real $q_1,q_2$ with $0\le q_1<q_2$, $H_N(q_1)<H_N(q_2)$; and for every natural $N_1,N_2$ and real $q$ with $2\le N_1<N_2$ and $q\ge0$, $H_{N_1}(q)<H_{N_2}(q)$.
-- source:
--   Optimal Constant Stepsizes for the Exact PGD Residual Curve, manuscript dated 2026-10-30, Theorem 1, p. 1; proof p. 2; local source: 02_PGD_Optimal_Constant_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Stepsize
open PGDMap20261031

theorem PGDMap20261031.step_monotonicity : StepMonotonicityClaim := by sorry
