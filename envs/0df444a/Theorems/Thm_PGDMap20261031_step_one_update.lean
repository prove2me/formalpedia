-- Prove2me | Theorems.Thm_PGDMap20261031_step_one_update
-- name    : PGDMap20261031.step_one_update
-- status  : Proved
-- author  : @Somehow
-- created : 2026-10-31T13:04:04.556477+00:00
-- url     : https://prove2.me/theorems/7fe4c260-18f7-4fe2-8008-7c4e82fa4f48
-- title:
--   One-update optimum and the open-endpoint case
-- statement:
--   ## Statement
--
--   For real $h,q$, the one-update curve is $C_1(h,q)=2/[h(2-h+hq)]$, and real division by zero is $0$. The real infimum operation is total, taking value $0$ on the empty set or on a set unbounded below. For every real $q$ with $0\le q<1/2$, the real number $h_*=1/(1-q)$ lies in $(0,2)$ and $2/[h_*(2-h_*+h_*q)]<2/[u(2-u+uq)]$ for every real $u\in(0,2)$ different from $h_*$. For every real $q\ge1/2$ and every real $h\in(0,2)$ there exists a real $u\in(0,2)$ with $2/[u(2-u+uq)]<2/[h(2-h+hq)]$, and, as a real $h$ tends to $2$ from below, $2/[h(2-h+hq)]$ tends to the total real infimum of the set $\{2/[u(2-u+uq)]:u\in(0,2)\}$. Thus the second clause includes $q=1/2$ and its limit is taken at the excluded endpoint $2$; it asserts no attained minimum.
-- source:
--   Optimal Constant Stepsizes for the Exact PGD Residual Curve, manuscript dated 2026-10-30, Theorem 1, p. 1; proof p. 2; local source: 02_PGD_Optimal_Constant_Stepsize.pdf

import Definitions.Def_PGDMap20261031_Stepsize
open PGDMap20261031

theorem PGDMap20261031.step_one_update : OneUpdateClaim := by sorry
