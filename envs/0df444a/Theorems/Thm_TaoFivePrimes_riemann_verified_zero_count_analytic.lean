-- Prove2me | Theorems.Thm_TaoFivePrimes_riemann_verified_zero_count_analytic
-- name    : TaoFivePrimes.riemann_verified_zero_count_analytic
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T03:41:19.863678+00:00
-- url     : https://prove2.me/theorems/d3755ecc-0523-47a9-ae46-ec25cb18ebb2
-- title:
--   Riemann--von Mangoldt count of zeta zeros in the verified window is at most 10^10
-- statement:
--   Set $T_0 = 3.29\times 10^9 = 329\times 10^7$. Counting zeros of the Riemann zeta function with their orders of vanishing in the closed strip $0\le\operatorname{Re}\rho\le 1$, $0\le\operatorname{Im}\rho\le T_0$, the multiplicity-weighted count satisfies
--
--   $$\sum_{\substack{\zeta(\rho)=0\\0\le\operatorname{Re}\rho\le1\\0\le\operatorname{Im}\rho\le T_0}}\operatorname{ord}_\rho\zeta\ \le\ 10^{10}.$$
--
--   This is the Riemann--von Mangoldt count input of Theorem 1.5 of Tao's paper (arXiv:1201.6656v4), obtained by summing the main theorem `Zeta23.RvM.rvM_main_param` over the 29 dyadic steps below $T_0$. Write $N(T)$ for the window count with multiplicity and $N(I')=N(T/2^{29},2T/2^{29})$; the local count at `zetaZeroConfig` gives $N(t,t+1)\le 200\log(|t|+3)$ and the B\"acklund bound gives $|S(T)|\le 1000\log T$, so each dyadic step contributes at most $M(2t)-M(t)+3845\log t$ with $M(t)=\tfrac{t}{2\pi}\log\tfrac{t}{2\pi e}$. The base case $N(0,7)=0$ uses an explicit zero-free rectangle of height $6$ in the open critical strip. Since $\log T_0\le 22$ and $\log\frac{T_0}{2\pi e}\le\frac{477}{25}$, the geometric sum is at most $10^{10}$ by elementary arithmetic.
--
--   Multiplicity is carried by `analyticOrderNatAt`, which is what the explicit formula and the major-arc analysis of Proposition 7.2 require.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 7, paragraph immediately following Proposition 7.2, equations (7.3)-(7.4), printed p.34; the zero sum in its proof counts multiplicities. The count itself is Riemann--von Mangoldt, Riem-von Mangoldt, Acta Math. 97 (1957) 1-52, instantiated at the platform's hypothesis-free `zetaZeroConfig`. https://arxiv.org/html/1201.6656v4#S7

import Mathlib
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Theorems.Thm_Zeta23_RvM_rvM_main_param
import Theorems.Thm_Zeta23_RvM_reZeroSet_card_le_of_growth
import Theorems.Thm_Zeta23_RvM_backlund_horizontal_of_count_at
import Theorems.Thm_Zeta23_RvM_zeta_growth_right_at
import Theorems.Thm_Zeta23_RvM_vertical_two
import Theorems.Thm_Zeta23_mu_smooth
import Theorems.Thm_Zeta23_MuInts_integral_main_eq
import Theorems.Thm_Zeta23_ZeroConfig_N_le_two_mul_half

open Complex Set Filter Topology Metric MeasureTheory Real
open scoped BigOperators
open Zeta23 Zeta23.RvM

theorem TaoFivePrimes.riemann_verified_zero_count_analytic :
    (∑ᶠ s ∈ {s : ℂ | riemannZeta s = 0 ∧ 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧
        s.im ≤ 3.29 * 10 ^ 9}, (analyticOrderNatAt riemannZeta s : ℝ)) ≤ (10 : ℝ) ^ 10 := by
  sorry
