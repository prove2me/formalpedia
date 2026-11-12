-- Prove2me | Theorems.Thm_PGDMap20261031_step_balance
-- name    : PGDMap20261031.step_balance
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:06.190006+00:00
-- url     : https://prove2.me/theorems/08313561-b58a-4d1d-bbe4-3007b8538c06
-- title:
--   Unique balance point and optimal constant stepsize
-- statement:
--   ## Statement
--
--   For natural $N$ and real $q,h$, write $A_N(h,q)=2/[h(2N-h)]$ if $q=0$ and $A_N(h,q)=2q/[(1+hq)^{2N}-1-h^2q]$ otherwise, and $B_N(h,q)=2(1+q)(1-h)^{\,2N-2}/[(1+hq)^{2N}-(1-h)^{2N}]$, where the exponent $2N-2$ is truncated at $0$. Write $C_N(h,q)=2/[h(2-h+hq)]$ if $N=1$, and $\max\{A_N(h,q),B_N(h,q)\}$ otherwise, and define $H_N(q)=\inf\{h\in\mathbb R:1<h<2,\ A_N(h,q)=B_N(h,q)\}$ using the total real infimum operation (in particular, the infimum of the empty set is $0$); all real division, including division by zero, is total, with $a/0=0$. For every natural $N\ge2$ and real $q\ge0$, $1<H_N(q)<2$, $0<H_N(q)<2$, $C_N(H_N(q),q)<C_N(u,q)$ for every real $u$ with $0<u<2$ and $u\ne H_N(q)$, $A_N(H_N(q),q)=B_N(H_N(q),q)$, and every real $h$ with $1<h<2$ and $A_N(h,q)=B_N(h,q)$ equals $H_N(q)$.
-- source:
--   Optimal Constant Stepsizes for the Exact PGD Residual Curve, manuscript dated 2026-10-30, Theorem 1, p. 1; proof p. 2; local source: 02_PGD_Optimal_Constant_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Stepsize
open PGDMap20261031

theorem PGDMap20261031.step_balance : StepBalanceClaim := by sorry
