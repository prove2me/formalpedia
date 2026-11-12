-- Prove2me | Theorems.Thm_PGDMap20261031_step_scalar_equations
-- name    : PGDMap20261031.step_scalar_equations
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:03:57.207364+00:00
-- url     : https://prove2.me/theorems/6d887428-5baf-450f-b674-6fba984e76fb
-- title:
--   Scalar equations characterizing the optimum
-- statement:
--   ## Statement
--
--   For natural $N$ and real $q,h$, write $A_N(h,q)=2/[h(2N-h)]$ if $q=0$ and $A_N(h,q)=2q/[(1+hq)^{2N}-1-h^2q]$ otherwise, and $B_N(h,q)=2(1+q)(1-h)^{\,2N-2}/[(1+hq)^{2N}-(1-h)^{2N}]$, where the exponent $2N-2$ is truncated at $0$. Write $C_N(h,q)=2/[h(2-h+hq)]$ if $N=1$, and $\max\{A_N(h,q),B_N(h,q)\}$ otherwise, and define $H_N(q)=\inf\{h\in\mathbb R:1<h<2,\ A_N(h,q)=B_N(h,q)\}$ using the total real infimum operation (in particular, the infimum of the empty set is $0$); all real division, including division by zero, is total, with $a/0=0$. For every natural $N\ge2$ and real $q,h$ with $q\ge0$ and $1<h<2$, $h=H_N(q)$ if and only if the following equation holds: when $q=0$, $(h-1)^{2(N-1)}[1+2(N-1)h]=1$; when $q\ne0$ (hence $q>0$ under the hypotheses), $(h-1)^{2(N-1)}=q/[1+q-(1+hq)^{-2(N-1)}]$. In the last expression the exponent is an integer negative power, hence the reciprocal of $(1+hq)^{2(N-1)}$; $N-1$ is subtraction in $\mathbb N$ and is at least $1$ under these hypotheses.
-- source:
--   Optimal Constant Stepsizes for the Exact PGD Residual Curve, manuscript dated 2026-10-30, Theorem 1, p. 1; proof p. 2; local source: 02_PGD_Optimal_Constant_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Stepsize
open PGDMap20261031

theorem PGDMap20261031.step_scalar_equations : StepRootEquationsClaim := by sorry
