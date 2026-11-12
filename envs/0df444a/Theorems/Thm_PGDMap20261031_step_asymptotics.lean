-- Prove2me | Theorems.Thm_PGDMap20261031_step_asymptotics
-- name    : PGDMap20261031.step_asymptotics
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:59.860314+00:00
-- url     : https://prove2.me/theorems/a910a879-38fa-485b-939a-9b26c56ed33c
-- title:
--   Long-horizon limits and asymptotic expansions
-- statement:
--   ## Statement
--
--   For natural $N$ and real $q,h$, write $A_N(h,q)=2/[h(2N-h)]$ if $q=0$ and $A_N(h,q)=2q/[(1+hq)^{2N}-1-h^2q]$ otherwise, and $B_N(h,q)=2(1+q)(1-h)^{\,2N-2}/[(1+hq)^{2N}-(1-h)^{2N}]$, where the exponent $2N-2$ is truncated at $0$. Write $C_N(h,q)=2/[h(2-h+hq)]$ if $N=1$, and $\max\{A_N(h,q),B_N(h,q)\}$ otherwise, and define $H_N(q)=\inf\{h\in\mathbb R:1<h<2,\ A_N(h,q)=B_N(h,q)\}$ using the total real infimum operation (in particular, the infimum of the empty set is $0$); all real division, including division by zero, is total, with $a/0=0$. For every fixed real $q\ge0$, $H_{n+2}(q)\to2$ as the natural number $n\to\infty$; for every fixed real $q>0$, $2(n+1)[2-H_{n+2}(q)]\to\log(1+1/q)$; and, without any further parameter, $2(n+1)[2-H_{n+2}(0)]-\log(4(n+1))\to0$. The integers $n+1$ are regarded as real numbers in these expressions and the sequence indices start at $N=n+2\ge2$.
-- source:
--   Optimal Constant Stepsizes for the Exact PGD Residual Curve, manuscript dated 2026-10-30, Theorem 1, p. 1; proof p. 2; local source: 02_PGD_Optimal_Constant_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Stepsize
open PGDMap20261031

theorem PGDMap20261031.step_asymptotics : StepAsymptoticsClaim := by sorry
